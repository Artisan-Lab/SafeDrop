use rustc_data_structures::{fx::FxHashMap, stable_set::FxHashSet};

#[derive(Debug,Clone)]
pub struct Node{
    pub index: usize,
    pub local: usize,
    need_drop: bool,
    so_so:bool,
    pub kind: usize,
    pub father: usize,
    pub alias: Vec<usize>,
    pub alive: isize,
    pub sons: FxHashMap<usize, usize>,
    pub field_info: Vec<usize>,
}

impl Node{
    pub fn new(index: usize, local: usize, need_drop: bool, so_so: bool) -> Node{
        let mut eq = Vec::new();
        eq.push(local);
        Node { index: index, local: local, need_drop: need_drop, father: local, alias: eq, alive: 0, so_so: so_so, kind: 0, sons: FxHashMap::default(), field_info: Vec::<usize>::new()}
    }

    pub fn need_drop(&self) -> bool{
        return self.need_drop;
    }

    pub fn so_so(&self) -> bool{
        return self.so_so;
    }

    pub fn dead(&mut self){
        self.alive = -1;
    }

    pub fn is_alive(&self) -> bool{
        return self.alive > -1;
    }

    pub fn is_tuple(&self)-> bool{
        return self.kind == 2;
    }

    pub fn is_ptr(&self)-> bool{
        return self.kind == 1 || self.kind == 4;
    }

    pub fn is_ref(&self)-> bool{
        return self.kind == 4;
    }

    pub fn is_corner_case(&self)-> bool{
        return self.kind == 3;
    }
}

#[derive(Debug,Clone)]
pub struct ReturnAssign{
    pub left_index: usize,
    pub left: Vec<usize>,
    pub left_so_so: bool, 
    pub left_need_drop: bool,
    pub right_index: usize,
    pub right: Vec<usize>,
    pub right_so_so: bool, 
    pub right_need_drop: bool,
    pub atype: usize,
}

impl ReturnAssign{
    pub fn new(atype: usize, left_index: usize, left_so_so: bool, left_need_drop: bool,
        right_index: usize, right_so_so: bool, right_need_drop: bool) -> ReturnAssign{
        let left = Vec::<usize>::new();
        let right = Vec::<usize>::new();
        ReturnAssign{
            left_index: left_index,
            left: left,
            left_so_so: left_so_so,
            left_need_drop: left_need_drop,
            right_index: right_index,
            right: right,
            right_so_so: right_so_so,
            right_need_drop: right_need_drop,
            atype: atype
        }
    }

    pub fn valuable(&self) -> bool{
        return self.left_so_so && self.right_so_so;
    }
}

#[derive(Clone)]
pub struct ReturnResults{
    pub arg_size: usize,
    pub assignments: Vec<ReturnAssign>,
    pub dead: FxHashSet<usize>,
}

impl ReturnResults {
    pub fn new(arg_size: usize) -> ReturnResults{
        let assignments = Vec::<ReturnAssign>::new();
        let dead = FxHashSet::default();
        ReturnResults { arg_size: arg_size, assignments: assignments, dead: dead }
    }
}
