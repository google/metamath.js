include "chil.mm"
include "wcel.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cort.mm"
include "wceq.mm"
include "c0v.mm"
include "cif.mm"
include "sneq.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "ifhvhv0.mm"
include "spansni.mm"
include "dedth.mm"

theorem spansn
  let cA: class A


  assert |- ( A e. ~H -> ( span ` { A } ) = ( _|_ ` ( _|_ ` { A } ) ) )

  proof
    cA
    chil
    wcel
    #
    cA
    csn
    #
    cspn
    cfv
    #
    @1
    cort
    cfv
    #
    cort
    cfv
    #
    wceq
    @0
    cA
    c0v
    cif
    #
    csn
    #
    cspn
    cfv
    #
    @6
    cort
    cfv
    #
    cort
    cfv
    #
    wceq
    cA
    c0v
    cA
    @5
    wceq
    #
    @2
    @7
    @4
    @9
    @10
    @1
    @6
    cspn
    cA
    @5
    sneq
    #
    fveq2d
    @10
    @3
    @8
    cort
    @10
    @1
    @6
    cort
    @11
    fveq2d
    fveq2d
    eqeq12d
    @5
    cA
    ifhvhv0
    spansni
    dedth
end
