
use crate::SafeDropGraph;
use rustc_data_structures::fx::FxHashSet;
use rustc_span::def_id::DefId;


impl<'tcx> SafeDropGraph<'tcx>{
    //can also use the format to check.
    //these function calls are the functions whose MIRs can not be fetched.
    pub fn corner_handle(&mut self, _left_ssa: usize, _merge_vec: &Vec::<usize>, _move_set: &mut FxHashSet<usize>, def_id: DefId) -> bool{
        // function::call_mut
        if def_id.index.as_usize() == 3430{
            return true;
        }
        //function::iterator::next
        if def_id.index.as_usize() == 8476{
            return true;
        }
        //intrinsic_offset
        if def_id.index.as_usize() == 1709{
            return true;
        }
        return false;
    }

    //the dangling pointer occuring in some functions like drop() is reasonable. 
    pub fn should_check(def_id: DefId) -> bool{
        let def_str = format!("{:?}",def_id);
        if let Some(_) = def_str.find("drop"){
            return false;
        }
        if let Some(_) = def_str.find("dealloc"){
            return false;
        }
        if let Some(_) = def_str.find("release"){
            return false;
        }
        if let Some(_) = def_str.find("destroy"){
            return false;
        }
        return true;
    }
}

//these adt structs use the Rc-kind drop instruction, which we do not focus on. 
pub fn is_corner_adt(str: String) -> bool{
    if let Some(_) = str.find("cell::RefMut"){
        return true;
    }
    if let Some(_) = str.find("cell::Ref"){
        return true;
    }
    if let Some(_) = str.find("rc::Rc"){
        return true;
    }
    return false;
}