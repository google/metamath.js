include "wbr.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "ssbri.mm"
include "brxp.mm"
include "sylib.mm"

theorem brel
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  assume brel.1: |- R C_ ( C X. D )


  assert |- ( A R B -> ( A e. C /\ B e. D ) )

  proof
    cA
    cB
    cR
    wbr
    cA
    cB
    cC
    cD
    cxp
    #
    wbr
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    cR
    @0
    cA
    cB
    brel.1
    ssbri
    cA
    cB
    cC
    cD
    brxp
    sylib
end
