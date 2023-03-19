include "cch.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "chil.mm"
include "wceq.mm"
include "cif.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqeq1d.mm"
include "ifchhv.mm"
include "chjoi.mm"
include "dedth.mm"

theorem chjo
  let cA: class A


  assert |- ( A e. CH -> ( A vH ( _|_ ` A ) ) = ~H )

  proof
    cA
    cch
    wcel
    #
    cA
    cA
    cort
    cfv
    #
    chj
    co
    #
    chil
    wceq
    @0
    cA
    chil
    cif
    #
    @3
    cort
    cfv
    #
    chj
    co
    #
    chil
    wceq
    cA
    chil
    cA
    @3
    wceq
    #
    @2
    @5
    chil
    @6
    cA
    @3
    @1
    @4
    chj
    @6
    id
    cA
    @3
    cort
    fveq2
    oveq12d
    eqeq1d
    @3
    cA
    ifchhv
    chjoi
    dedth
end
