// rust/compiler/rustc_mir_transform/lib.rs
// need to modify
+ pub mod safedrop_check;
+ use safedrop_check::{SafeDropGraph, FuncMap};
...
pub fn provide(providers: &mut Providers) {
    ...
    *providers = Providers {
        ...
        optimized_mir,
        is_mir_available,
        + safedrop_check,
        ...
    };
}


// add a pass function safedrop_check()
fn safedrop_check<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> () {
    if let Some(_other) = tcx.hir().body_const_context(def_id.expect_local()){
        return;
    }
    if tcx.is_mir_available(def_id) {
        let body = tcx.optimized_mir(def_id);
        let mut func_map = FuncMap::new();
        let mut safedrop_graph = SafeDropGraph::new(&body, tcx, def_id);
        safedrop_graph.solve_scc();
        safedrop_graph.safedrop_check(0, tcx, &mut func_map);
        if safedrop_graph.visit_times <= 10000{
            safedrop_graph.output_warning();
        }
        else{
            println!("over_visited: {:?}", def_id);
        }
    }
}