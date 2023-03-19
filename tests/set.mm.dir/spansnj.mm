include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "wceq.mm"
include "cif.mm"
include "c0v.mm"
include "oveq1.mm"
include "eqeq12d.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "ifchhv.mm"
include "ifhvhv0.mm"
include "spansnji.mm"
include "dedth2h.mm"

theorem spansnj
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. ~H ) -> ( A +H ( span ` { B } ) ) = ( A vH ( span ` { B } ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    cB
    csn
    #
    cspn
    cfv
    #
    cph
    co
    #
    cA
    @3
    chj
    co
    #
    wceq
    @0
    cA
    chil
    cif
    #
    @3
    cph
    co
    #
    @6
    @3
    chj
    co
    #
    wceq
    @6
    @1
    cB
    c0v
    cif
    #
    csn
    #
    cspn
    cfv
    #
    cph
    co
    #
    @6
    @11
    chj
    co
    #
    wceq
    cA
    cB
    chil
    c0v
    cA
    @6
    wceq
    @4
    @7
    @5
    @8
    cA
    @6
    @3
    cph
    oveq1
    cA
    @6
    @3
    chj
    oveq1
    eqeq12d
    cB
    @9
    wceq
    #
    @7
    @12
    @8
    @13
    @14
    @3
    @11
    @6
    cph
    @14
    @2
    @10
    cspn
    cB
    @9
    sneq
    fveq2d
    #
    oveq2d
    @14
    @3
    @11
    @6
    chj
    @15
    oveq2d
    eqeq12d
    @6
    @9
    cA
    ifchhv
    cB
    ifhvhv0
    spansnji
    dedth2h
end
