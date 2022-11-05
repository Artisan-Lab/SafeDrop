use std::vec::Vec;
use std::cmp::min;
use rustc_middle::mir::StatementKind;
use rustc_middle::mir::terminator::TerminatorKind;
use rustc_middle::mir::Body;
use rustc_middle::mir::BasicBlock;
use rustc_middle::mir::Local;
use rustc_middle::mir::Terminator;
use rustc_middle::mir::Place;
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::DefId;
use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::fx::FxHashMap;
use rustc_middle::mir::Operand;
use rustc_middle::mir::Rvalue;
use rustc_span::Span;
use super::BugRecords;
use super::tools::*;
use super::node::Node;
use super::node::ReturnResults;


//self-defined assignments structure. 
#[derive(Debug,Clone)]
pub struct Assignment<'tcx>{
    pub left: Place<'tcx>,
    pub right: Place<'tcx>,
    pub atype: usize,
    pub span: Span,
}

impl<'tcx> Assignment<'tcx>{
    pub fn new(left: Place<'tcx>, right: Place<'tcx>, atype: usize, span: Span)->Assignment<'tcx>{
        Assignment{
            left: left,
            right: right,
            atype: atype,
            span: span,
        }
    }
}

//self-defined basicblock structure.
#[derive(Debug,Clone)]
pub struct BlockNode<'tcx>{
    pub index: usize,
    pub is_cleanup: bool,
    pub next: FxHashSet<usize>,
    pub assignments: Vec<Assignment<'tcx>>,
    pub calls: Vec<Terminator<'tcx>>,
    pub drops: Vec<Terminator<'tcx>>,
    //store the index of the sub-blocks as the current node is the root node of a SCC. 
    pub sub_blocks: Vec<usize>,
    //store the const value defined in this block;
    pub const_value: Vec::<(usize, usize)>,
    //store switch stmts in current block for the path filtering in path-sensitive analysis.
    pub switch_stmts: Vec::<Terminator<'tcx>>,
}

impl<'tcx> BlockNode<'tcx>{
    pub fn new(index:usize, is_cleanup: bool) -> BlockNode<'tcx>{
        BlockNode{
            index: index,
            is_cleanup: is_cleanup,
            next: FxHashSet::<usize>::default(),
            assignments: Vec::<Assignment<'tcx>>::new(),
            calls: Vec::<Terminator<'tcx>>::new(),
            drops: Vec::<Terminator<'tcx>>::new(),
            sub_blocks: Vec::<usize>::new(),
            const_value: Vec::<(usize, usize)>::new(),
            switch_stmts: Vec::<Terminator<'tcx>>::new(),
        }
    }

    pub fn push(&mut self, index: usize){
        self.next.insert(index);
    }
}

pub struct SafeDropGraph<'tcx>{
    pub def_id: DefId,
    pub span: Span,
    // contains all varibles (including fields) as nodes.
    pub nodes: Vec<Node>,
    // contains all blocks in the CFG
    pub blocks: Vec<BlockNode<'tcx>>,
    pub arg_size: usize, 
    // we shrink a SCC into a node and use a father node to represent the SCC.
    pub father_block: Vec<usize>,
    // record the constant value during safedrop checking.
    pub constant_bool: FxHashMap<usize, usize>,
    // used for tarjan algorithmn.
    pub count: usize,
    // contains the return results for inter-procedure analysis.
    pub return_results: ReturnResults,
    // used for filtering duplicate alias assignments in return results.
    pub return_set: FxHashSet<(usize, usize)>,
    // record the information of bugs for the function.
    pub bug_records: BugRecords,
    // a threhold to avoid path explosion.
    pub visit_times: usize
}

impl<'tcx> SafeDropGraph<'tcx>{
    pub fn new(my_body: &Body<'tcx>,  tcx: TyCtxt<'tcx>, def_id: DefId) -> SafeDropGraph<'tcx>{  
        // handle variables
        let locals = &my_body.local_decls;
        let arg_size = my_body.arg_count;
        let mut nodes = Vec::<Node>::new();
        let param_env = tcx.param_env(def_id);
        for ld in 0..locals.len() {
            let temp = Local::from(ld);
            let need_drop = locals[temp].ty.needs_drop(tcx, param_env);
            let so_so = so_so(locals[temp].ty);
            let mut node = Node::new(ld, ld, need_drop, need_drop || !so_so);
            node.kind = kind(locals[temp].ty);
            nodes.push(node);
        }
        
        let basicblocks = my_body.basic_blocks();
        let mut blocks = Vec::<BlockNode<'tcx>>::new();
        let mut father_block = Vec::<usize>::new();
        
        // handle each basicblock
        for i in 0..basicblocks.len(){
            father_block.push(i);
            let iter = BasicBlock::from(i);
            let terminator = basicblocks[iter].terminator.clone().unwrap();
            let mut current_node = BlockNode::new(i, basicblocks[iter].is_cleanup);
            
            // handle general statements
            for statement in &basicblocks[iter].statements{
                if let StatementKind::Assign(ref assign) = statement.kind {
                    let left_ssa = assign.0.local.as_usize();
                    let left = assign.0.clone();
                    match assign.1 {
                        Rvalue::Use(ref x) => {
                            match x {
                                Operand::Copy(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, 0, statement.source_info.span.clone());
                                        current_node.assignments.push(assign);
                                    }
                                },
                                Operand::Move(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, 1, statement.source_info.span.clone());
                                        current_node.assignments.push(assign);
                                    }
                                },
                                Operand::Constant(ref constant) => { 
                                    if let None = constant.literal.try_to_scalar(){
                                        continue;
                                    }
                                    if let Err(_tmp) = constant.literal.try_to_scalar().clone().unwrap().try_to_int(){
                                        continue;
                                    }
                                    if let Some(ans) = constant.literal.try_eval_usize(tcx, param_env){
                                        current_node.const_value.push((left_ssa, ans as usize));
                                        continue;
                                    }
                                    if let Some(const_bool) = constant.literal.try_to_bool() {
                                        current_node.const_value.push((left_ssa, const_bool as usize));
                                    }
                                    continue;
                                },
                            }
                        }
                        Rvalue::Ref(_, _, ref p) => {
                            let right_ssa = p.local.as_usize();
                            if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                let right = p.clone();
                                let assign = Assignment::new(left, right, 0, statement.source_info.span.clone());
                                current_node.assignments.push(assign);
                            }
                        },
                        Rvalue::AddressOf(_, ref p) => {
                            let right_ssa = p.local.as_usize();
                            if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                let right = p.clone();
                                let assign = Assignment::new(left, right, 0, statement.source_info.span.clone());
                                current_node.assignments.push(assign);
                            }
                        },
                        
                        Rvalue::ShallowInitBox(ref x, _) => {
                            if nodes[left_ssa].sons.contains_key(&0) == false{
                                let mut node = Node::new(left_ssa, nodes.len(), false, true);
                                let mut node1 = Node::new(left_ssa, nodes.len() + 1, false, true);
                                let mut node2 = Node::new(left_ssa, nodes.len() + 2, false, true);
                                node.alive = nodes[left_ssa].alive;
                                node1.alive = node.alive;
                                node2.alive = node.alive;
                                node.sons.insert(0, node1.local);
                                node.field_info.push(0);
                                node1.sons.insert(0, node2.local);
                                node1.field_info.push(0);
                                node1.field_info.push(0);
                                node2.field_info.push(0);
                                node2.field_info.push(0);
                                node2.field_info.push(0);
                                node2.kind = 1;
                                nodes[left_ssa].sons.insert(0, node.local);
                                nodes.push(node);
                                nodes.push(node1);
                                nodes.push(node2);
                            }
                            match x {
                                Operand::Copy(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, 2, statement.source_info.span.clone());
                                        current_node.assignments.push(assign);
                                    }
                                },
                                Operand::Move(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, 2, statement.source_info.span.clone());
                                        current_node.assignments.push(assign);
                                    }
                                },
                                Operand::Constant(_) => {},
                            }
                        },
                        Rvalue::Cast(_, ref x, _) => {
                            match x {
                                Operand::Copy(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, 0, statement.source_info.span.clone());
                                        current_node.assignments.push(assign);
                                    }
                                },
                                Operand::Move(ref p) => {
                                    let right_ssa = p.local.as_usize();
                                    if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                        let right = p.clone();
                                        let assign = Assignment::new(left, right, 1, statement.source_info.span.clone());
                                        current_node.assignments.push(assign);
                                    }
                                },
                                Operand::Constant(_) => {},
                            }
                        },
                        Rvalue::Aggregate(_, ref x) => {
                            for each_x in x {
                                match each_x {
                                    Operand::Copy(ref p) => {
                                        let right_ssa = p.local.as_usize();
                                        if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                            let right = p.clone();
                                            let assign = Assignment::new(left, right, 0, statement.source_info.span.clone());
                                            current_node.assignments.push(assign);
                                        }
                                    },
                                    Operand::Move(ref p) => {
                                        let right_ssa = p.local.as_usize();
                                        if nodes[left_ssa].so_so() && nodes[right_ssa].so_so(){
                                            let right = p.clone();
                                            let assign = Assignment::new(left, right, 0, statement.source_info.span.clone());
                                            current_node.assignments.push(assign);
                                        }
                                    },
                                    Operand::Constant(_) => {},
                                }
                            }
                        },
                        Rvalue::Discriminant(ref p) => {
                            let right = p.clone();
                            let assign = Assignment::new(left, right, 3, statement.source_info.span.clone());
                            current_node.assignments.push(assign);
                        }
                        _ => {}
                    }
                }
            }

            // handle terminator statements
            match terminator.kind {
                TerminatorKind::Goto { ref target } => {
                    current_node.push(target.as_usize());
                },
                TerminatorKind::SwitchInt{ discr: _, switch_ty: _, ref targets } => {
                    current_node.switch_stmts.push(terminator.clone());
                    for (_, ref target) in targets.iter() {
                        current_node.push(target.as_usize());
                    }
                    current_node.push(targets.otherwise().as_usize());
                }, 
                TerminatorKind::Resume => {},
                TerminatorKind::Return => {},
                TerminatorKind::Abort
                | TerminatorKind::GeneratorDrop
                | TerminatorKind::Unreachable => {}
                TerminatorKind::Drop { place: _, ref target, ref unwind } => {
                    current_node.push(target.as_usize());
                    current_node.drops.push(terminator.clone());
                    if let Some(target) = unwind {
                        current_node.push(target.as_usize());
                    }
                },
                TerminatorKind::DropAndReplace { place: _, value: _, ref target, ref unwind } => {
                    current_node.push(target.as_usize());
                    if let Some(target) = unwind {
                        current_node.push(target.as_usize());
                    }
                },
                TerminatorKind::Call { func: _, args: _, destination: _, ref target, ref cleanup, from_hir_call: _, fn_span: _ } => {
                    if let Some(tt) = target {
                        current_node.push(tt.as_usize());
                    }
                    if let Some(tt) = cleanup {
                        current_node.push(tt.as_usize());
                    }
                    current_node.calls.push(terminator.clone());
                },
                TerminatorKind::Assert { cond: _, expected: _, msg: _, ref target, ref cleanup } => {
                    current_node.push(target.as_usize());
                    if let Some(target) = cleanup {
                        current_node.push(target.as_usize());
                    }
                },
                TerminatorKind::Yield { value: _, ref resume, resume_arg: _, ref drop } => {
                    current_node.push(resume.as_usize());
                    if let Some(target) = drop {
                        current_node.push(target.as_usize());
                    }
                },
                TerminatorKind::FalseEdge { ref real_target, imaginary_target: _ } => {
                    current_node.push(real_target.as_usize());
                },
                TerminatorKind::FalseUnwind { ref real_target, unwind: _ } => {
                    current_node.push(real_target.as_usize());
                },
                TerminatorKind::InlineAsm { template: _, operands: _, options: _, line_spans: _, ref destination, ref cleanup} => {
                    if let Some(target) = destination {
                        current_node.push(target.as_usize());
                    }
                    if let Some(target) = cleanup {
                        current_node.push(target.as_usize());
                    }
                }
            }
            blocks.push(current_node);
        }

        SafeDropGraph{
            def_id: def_id.clone(),
            span: my_body.span,
            blocks: blocks,
            nodes: nodes,
            arg_size: arg_size,
            father_block: father_block,
            constant_bool: FxHashMap::default(), 
            count: 0,
            return_results: ReturnResults::new(arg_size),
            return_set: FxHashSet::default(),
            bug_records: BugRecords::new(),
            visit_times: 0,
        }
    }

    pub fn tarjan(&mut self, index: usize,
        stack: &mut Vec<usize>, 
        instack: &mut FxHashSet<usize>,
        dfn: &mut Vec<usize>,
        low: &mut Vec<usize>){
        dfn[index] = self.count;
        low[index] = self.count;
        self.count += 1;
        instack.insert(index);
        stack.push(index);
        let out_set = self.blocks[index].next.clone();    
        for i in out_set{
            let target = i;
            if dfn[target] == 0{
                self.tarjan(target, stack, instack, dfn, low);
                low[index] = min(low[index], low[target]);
            }
            else{
                if instack.contains(&target){
                    low[index] = min(low[index], dfn[target]);
                }
            }
        }
        // generate SCC
        if dfn[index] == low[index]{
            loop{
                let top = stack.pop().unwrap();
                self.father_block[top] = index;
                instack.remove(&top);
                if index == top{
                    break;
                }
                let top_node = self.blocks[top].next.clone();
                for i in top_node{self.blocks[index].next.insert(i);}
                self.blocks[index].sub_blocks.push(top);
                for i in self.blocks[top].sub_blocks.clone(){
                    self.blocks[index].sub_blocks.push(i);
                }
            } 
            self.blocks[index].sub_blocks.reverse();
            //remove the out nodes which is in the current SCC
            let mut remove_list = Vec::new();
            for i in self.blocks[index].next.iter(){
                if self.father_block[*i] == index{
                    remove_list.push(*i);
                }
            }
            for i in remove_list{
                self.blocks[index].next.remove(&i);
            }
        }
    }

    // handle SCC
    pub fn solve_scc(&mut self){
        let mut stack = Vec::<usize>::new();
        let mut instack = FxHashSet::<usize>::default();
        let mut dfn = vec![0 as usize; self.blocks.len()];
        let mut low = vec![0 as usize; self.blocks.len()];
        self.tarjan(0, &mut stack, &mut instack, &mut dfn, &mut low);
    }
}
