include "wrel.mm"
include "wbr.mm"
include "wa.mm"
include "cvv.mm"
include "wcel.mm"
include "brrelex12.mm"
include "simpld.mm"

theorem brrelex
  let cA: class A
  let cB: class B
  let cR: class R


  assert |- ( ( Rel R /\ A R B ) -> A e. _V )

  proof
    cR
    wrel
    cA
    cB
    cR
    wbr
    wa
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cR
    brrelex12
    simpld
end
