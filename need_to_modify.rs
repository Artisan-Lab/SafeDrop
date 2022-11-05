// rust/compiler/rustc_middle/src/query/mod.rs
rustc_queries! {
    query trigger_delay_span_bug(key: DefId) -> () {
        desc { "trigger a delay span bug" }
    }
    + query safedrop_check(_: DefId) -> () {
    +    desc { "check safedrop bugs in rustc mir" }
    + }
    ...
}



// rust/compiler/rustc_interface/src/passes.rs
fn analysis(tcx: TyCtxt<'_>, (): ()) -> Result<()> {
    ...
    sess.time("layout_testing", || layout_test::test_layout(tcx));

    + sess.time("safedrop_check", || {
    +   tcx.hir().par_body_owners(|def_id| tcx.ensure().safedrop_check(def_id));
    + });
}