include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cr.mm"
include "eleei.mm"
include "ffvelrnda.mm"

theorem fveere
  let cA: class A
  let cI: class I
  let cN: class N


  assert |- ( ( A e. ( EE ` N ) /\ I e. ( 1 ... N ) ) -> ( A ` I ) e. RR )

  proof
    cA
    cN
    cee
    cfv
    wcel
    c1
    cN
    cfz
    co
    cr
    cI
    cA
    cA
    cN
    eleei
    ffvelrnda
end
