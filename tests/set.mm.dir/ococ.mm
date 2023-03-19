include "cch.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wceq.mm"
include "chil.mm"
include "cif.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "ifchhv.mm"
include "ococi.mm"
include "dedth.mm"

theorem ococ
  let cA: class A


  assert |- ( A e. CH -> ( _|_ ` ( _|_ ` A ) ) = A )

  proof
    cA
    cch
    wcel
    #
    cA
    cort
    cfv
    #
    cort
    cfv
    #
    cA
    wceq
    @0
    cA
    chil
    cif
    #
    cort
    cfv
    #
    cort
    cfv
    #
    @3
    wceq
    cA
    chil
    cA
    @3
    wceq
    #
    @2
    @5
    cA
    @3
    @6
    @1
    @4
    cort
    cA
    @3
    cort
    fveq2
    fveq2d
    @6
    id
    eqeq12d
    @3
    cA
    ifchhv
    ococi
    dedth
end
