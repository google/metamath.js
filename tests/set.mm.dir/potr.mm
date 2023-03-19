include "wpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wi.mm"
include "pocl.mm"
include "imp.mm"
include "simprd.mm"

theorem potr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R


  assert |- ( ( R Po A /\ ( B e. A /\ C e. A /\ D e. A ) ) -> ( ( B R C /\ C R D ) -> B R D ) )

  proof
    cA
    cR
    wpo
    #
    cB
    cA
    wcel
    cC
    cA
    wcel
    cD
    cA
    wcel
    w3a
    #
    wa
    cB
    cB
    cR
    wbr
    wn
    #
    cB
    cC
    cR
    wbr
    cC
    cD
    cR
    wbr
    wa
    cB
    cD
    cR
    wbr
    wi
    #
    @0
    @1
    @2
    @3
    wa
    cA
    cB
    cC
    cD
    cR
    pocl
    imp
    simprd
end
