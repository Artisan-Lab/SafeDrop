use rustc_middle::mir::SourceInfo;
use rustc_middle::ty;
use rustc_middle::ty::Ty;
use rustc_middle::mir::Place;
use rustc_middle::ty::TyCtxt;
use rustc_middle::mir::ProjectionElem;
use rustc_span::Span;
use rustc_data_structures::fx::FxHashMap;
use rustc_data_structures::fx::FxHashSet;
use super::Node;
use super::ReturnAssign;
use super::ReturnResults;
use super::SafeDropGraph;
use super::corner_handle::is_corner_adt;
use super::graph::BlockNode;
pub use std::fmt;


impl<'tcx> SafeDropGraph<'tcx>{
    pub fn output_warning(&self){
        if self.bug_records.is_bug_free(){
            return;
        }
        println!("=================================");
        println!("Function:{0:?};{1:?}", self.def_id, self.def_id.index);
        self.bug_records.df_bugs_output();
        self.bug_records.uaf_bugs_output();
        self.bug_records.dp_bug_output(self.span);
        
        println!();
        println!();
    }

    // assign to the variable _x, we will set the alive of _x and its child nodes a new alive.
    pub fn fill_alive(&mut self, node: usize, alive: isize){
        self.nodes[node].alive = alive;
        //TODO: check the correctness.
        for i in self.nodes[node].alias.clone(){
            if self.nodes[i].alive == -1{
                self.nodes[i].alive = alive;
            }
        }
        for i in self.nodes[node].sons.clone().into_iter(){
            self.fill_alive(i.1, alive);
        }
    }

    pub fn exist_dead(&self, node: usize, record: &mut FxHashSet<usize>, dangling: bool) -> bool{
        //if is a dangling pointer check, only check the pointer type varible.
        if self.nodes[node].is_alive() == false && (dangling && self.nodes[node].is_ptr() || !dangling){
            return true; 
        }
        record.insert(node);
        if self.nodes[node].alias[0] != node{
            for i in self.nodes[node].alias.clone().into_iter(){
                if i != node && record.contains(&i) == false && self.exist_dead(i, record, dangling){
                    return true;
                }
            }
        }
        for i in self.nodes[node].sons.clone().into_iter(){
            if record.contains(&i.1) == false && self.exist_dead(i.1, record, dangling){
                return true;
            }
        }
        return false;
    }

    pub fn df_check(&mut self, drop: usize, span: Span) -> bool{
        let root = self.nodes[drop].index;
        if self.nodes[drop].is_alive() == false 
        && self.bug_records.df_bugs.contains_key(&root) == false{
            self.bug_records.df_bugs.insert(root, span.clone());
        }
        return self.nodes[drop].is_alive() == false;
    }

    pub fn uaf_check(&mut self, used: usize, span: Span, origin: usize, is_func_call: bool){
        let mut record = FxHashSet::default();
        if self.nodes[used].so_so() && (!self.nodes[used].is_ptr() || self.nodes[used].index != origin || is_func_call) 
        && self.exist_dead(used, &mut record, false) == true 
        && self.bug_records.uaf_bugs.contains(&span) == false{            
            self.bug_records.uaf_bugs.insert(span.clone());
        }
    }

    pub fn dp_check(&self, local: usize) -> bool{
        let mut record = FxHashSet::default();
        return self.exist_dead(local, &mut record, local != 0);
    }

    pub fn bug_check(&mut self, current_block: &BlockNode<'tcx>){
        if current_block.is_cleanup == false{
            if self.nodes[0].so_so() && self.dp_check(0){
                self.bug_records.dp_bug = true;
            }
            else{
                for i in 0..self.arg_size{
                    if self.nodes[i+1].is_ptr() && self.dp_check(i+1){
                        self.bug_records.dp_bug = true;
                    }
                }
            }
        }
        else{
            for i in 0..self.arg_size{
                if self.nodes[i+1].is_ptr() && self.dp_check(i+1){
                    self.bug_records.dp_bug_unwind = true;
                }
            }
        }
    }

    pub fn dead_node(&mut self, drop: usize, life_begin: usize, info: &SourceInfo, alias: bool){
        //Rc drop
        if self.nodes[drop].is_corner_case(){
            return;
        }
        //check if there is a double free bug.
        if self.df_check(drop, info.span){
            return;
        }
        //drop their alias
        if self.nodes[drop].alias[0] != drop{
            for i in self.nodes[drop].alias.clone().into_iter(){
                if self.nodes[i].is_ref(){
                    continue;
                }
                self.dead_node(i, life_begin, info, true);
            }
        }
        //drop the sons of the root node.
        //alias flag is used to avoid the sons of the alias are dropped repeatly.
        if alias == false{
            for i in self.nodes[drop].sons.clone().into_iter(){
                if self.nodes[drop].is_tuple() == true && self.nodes[i.1].need_drop() == false{
                    continue;
                }
                self.dead_node( i.1, life_begin, info, false);
            }
        }
        //SCC.
        if self.nodes[drop].alive < life_begin as isize && self.nodes[drop].so_so(){
            self.nodes[drop].dead();   
        }
    }

    // field-sensitive fetch instruction for a variable.
    // is_right: 2 = 1.0; 0 = 2.0; => 0 = 1.0.0;   
    pub fn handle_projection(&mut self, is_right: bool, local: usize, tcx: TyCtxt<'tcx>, place: Place<'tcx>) -> usize{
        let mut init_local = local;
        let mut current_local = local;
        for projection in place.projection{
            match projection{
                ProjectionElem::Deref => {
                    if current_local == self.nodes[current_local].alias[0] && self.nodes[current_local].is_ref() == false{
                        let need_drop = true;
                        let so_so = true;
                        let mut node = Node::new(self.nodes.len(), self.nodes.len(), need_drop, need_drop || !so_so);
                        node.kind = 1; //TODO
                        node.alive = self.nodes[current_local].alive;
                        self.nodes[current_local].alias[0] = self.nodes.len();
                        self.nodes.push(node);
                    }
                    current_local = self.nodes[current_local].alias[0];
                    init_local = self.nodes[current_local].index;
                }
                ProjectionElem::Field(field, ty) =>{
                    let index = field.as_usize();
                    if is_right && self.nodes[current_local].alias[0] != current_local{
                        current_local = self.nodes[current_local].alias[0];
                        init_local = self.nodes[current_local].index;
                    }
                    if self.nodes[current_local].sons.contains_key(&index) == false{
                        let param_env = tcx.param_env(self.def_id);
                        let need_drop = ty.needs_drop(tcx, param_env);
                        let so_so = so_so(ty);
                        let mut node = Node::new(init_local, self.nodes.len(), need_drop, need_drop || !so_so);
                        node.kind = kind(ty);
                        node.alive = self.nodes[current_local].alive;
                        node.field_info = self.nodes[current_local].field_info.clone();
                        node.field_info.push(index);
                        self.nodes[current_local].sons.insert(index, node.local);
                        self.nodes.push(node);
                    }
                    current_local = *self.nodes[current_local].sons.get(&index).unwrap();
                }
                _ => {}
            }
        }
        return current_local;
    }

    //merge the result of current path to the final result.
    pub fn merge_results(&mut self, results_nodes: Vec<Node>, is_cleanup: bool){
        for node in results_nodes.iter(){
            if node.index <= self.arg_size{
                if node.alias[0] != node.local || node.alias.len() > 1{
                    for alias in node.alias.clone(){
                        if results_nodes[alias].index <= self.arg_size
                        && !self.return_set.contains(&(node.local, alias))
                        && alias != node.local
                        && node.index != results_nodes[alias].index{
                            self.return_set.insert((node.local, alias));
                            let left_node = node;
                            let right_node = &results_nodes[alias];
                            let mut new_assign = ReturnAssign::new(0, 
                                left_node.index, left_node.so_so(), left_node.need_drop(),
                                right_node.index, right_node.so_so(), right_node.need_drop());
                            new_assign.left = left_node.field_info.clone();
                            new_assign.right = right_node.field_info.clone();
                            self.return_results.assignments.push(new_assign);
                        }
                    }
                }
                if node.is_ptr() && is_cleanup == false && node.is_alive() == false && node.local <= self.arg_size{
                    self.return_results.dead.insert(node.local);
                }
            }
        }
    }
}

pub fn kind<'tcx>(current_ty: Ty<'tcx>) -> usize {
    match current_ty.kind() {
        ty::RawPtr(..) => 1,
        ty::Ref(..) => 4,
        ty::Tuple(..) => 2,
        ty::Adt(ref adt_def, _) => {
            if is_corner_adt(format!("{:?}", adt_def)){
                return 3;
            }
            else{
                return 0;
            }
        },
        _ => 0,
    }
}

//type filter.
pub fn so_so<'tcx>(current_ty: Ty<'tcx>) -> bool {
    match current_ty.kind() {
        ty::Bool
        | ty::Char
        | ty::Int(_)
        | ty::Uint(_)
        | ty::Float(_) => true,
        ty::Array(ref tys,_) => so_so(*tys),
        ty::Adt(_, ref substs) => {
            for tys in substs.types() {
                if !so_so(tys) {
                    return false;
                }
            }
            true
        },
        ty::Tuple(ref substs) => {
            for tys in substs.iter() {
                if !so_so(tys) {
                    return false;
                }
            }
            true
        },
        _ => false,
    }
}

//instruction to assign alias for a variable.
pub fn merge_alias(move_set: &mut FxHashSet<usize>, left_ssa: usize, right_ssa: usize, nodes: &mut Vec<Node>){
    if nodes[left_ssa].index == nodes[right_ssa].index{
        return;
    }
    if move_set.contains(&left_ssa){
        let mut alias_clone = nodes[right_ssa].alias.clone();
        nodes[left_ssa].alias.append(&mut alias_clone);
    }
    else{
        move_set.insert(left_ssa);
        nodes[left_ssa].alias = nodes[right_ssa].alias.clone();
    }
    for son in nodes[right_ssa].sons.clone().into_iter(){
        if nodes[left_ssa].sons.contains_key(&son.0) == false{
            let mut node = Node::new(nodes[left_ssa].index, nodes.len(), nodes[son.1].need_drop(), nodes[son.1].so_so());
            node.kind = nodes[son.1].kind;
            node.alive = nodes[left_ssa].alive;
            node.field_info = nodes[left_ssa].field_info.clone();
            node.field_info.push(son.0);
            nodes[left_ssa].sons.insert(son.0, node.local);
            nodes.push(node);
        }
        let l_son = *(nodes[left_ssa].sons.get(&son.0).unwrap());
        merge_alias(move_set, l_son, son.1, nodes);
    }
}

//inter-procedure instruction to merge alias.
pub fn merge(move_set: &mut FxHashSet<usize>, nodes: &mut Vec<Node>, assign: &ReturnAssign, arg_vec: &Vec<usize>){
    if assign.left_index >= arg_vec.len(){
        println!("vector warning!");
        return;
    }
    if assign.right_index >= arg_vec.len(){
        println!("vector warning!");
        return;
    }
    let left_init = arg_vec[assign.left_index];
    let mut right_init = arg_vec[assign.right_index];
    let mut left_ssa = left_init;
    let mut right_ssa = right_init;
    for index in assign.left.iter(){
        if nodes[left_ssa].sons.contains_key(&index) == false{
            let need_drop = assign.left_need_drop;
            let so_so = assign.left_so_so;
            let mut node = Node::new(left_init, nodes.len(), need_drop, so_so);
            node.kind = 1;
            node.alive = nodes[left_ssa].alive;
            node.field_info = nodes[left_ssa].field_info.clone();
            node.field_info.push(*index);
            nodes[left_ssa].sons.insert(*index, node.local);
            nodes.push(node);
        }
        left_ssa = *nodes[left_ssa].sons.get(&index).unwrap();
    }
    for index in assign.right.iter(){
        if nodes[right_ssa].alias[0] != right_ssa{
            right_ssa = nodes[right_ssa].alias[0];
            right_init = nodes[right_ssa].index;
        }
        if nodes[right_ssa].sons.contains_key(&index) == false{
            let need_drop = assign.right_need_drop;
            let so_so = assign.right_so_so;
            let mut node = Node::new(right_init, nodes.len(), need_drop, so_so);
            node.kind = 1;
            node.alive = nodes[right_ssa].alive;
            node.field_info = nodes[right_ssa].field_info.clone();
            node.field_info.push(*index);
            nodes[right_ssa].sons.insert(*index, node.local);
            nodes.push(node);
        }
        right_ssa = *nodes[right_ssa].sons.get(&index).unwrap();
    }
    merge_alias(move_set, left_ssa, right_ssa, nodes);
}

//struct to cache the results for analyzed functions.
#[derive(Clone)]
pub struct FuncMap {
    pub map: FxHashMap<usize, ReturnResults>,
    pub set: FxHashSet<usize>,
}

impl FuncMap{
    pub fn new() -> FuncMap{
        FuncMap { map: FxHashMap::default(), set: FxHashSet::default()}
    }
}

//structure to record the existed bugs.
pub struct BugRecords{
    pub df_bugs: FxHashMap<usize, Span>,
    pub df_bugs_unwind: FxHashMap<usize, Span>,
    pub uaf_bugs: FxHashSet<Span>,
    pub dp_bug: bool,
    pub dp_bug_unwind: bool,
}

impl BugRecords{
    pub fn new() -> BugRecords{
        BugRecords { df_bugs: FxHashMap::default(), df_bugs_unwind: FxHashMap::default(), uaf_bugs: FxHashSet::default(), dp_bug: false, dp_bug_unwind: false}
    }

    pub fn is_bug_free(&self) -> bool{
        return self.df_bugs.is_empty() && self.uaf_bugs.is_empty() && self.dp_bug == false && self.dp_bug_unwind == false;
    }

    pub fn df_bugs_output(&self){
        if self.df_bugs.is_empty(){
            return;
        }
        println!("Double Free Bugs Exist:");
        for i in self.df_bugs.iter(){
            println!("occurs in {:?}", i.1);
        }
    }

    pub fn uaf_bugs_output(&self){
        if self.uaf_bugs.is_empty(){
            return;
        }
        println!("Use After Free Bugs Exist:");
        for i in self.uaf_bugs.iter(){
            println!("occurs in {:?}", i);
        }
    }

    pub fn dp_bug_output(&self, span: Span){
        if self.dp_bug{
            println!("Dangling Pointer Bug Exist {:?}", span);
        }
        if self.dp_bug_unwind{
            println!("Dangling Pointer Bug Exist in Unwinding {:?}", span);
        }
    }
}
