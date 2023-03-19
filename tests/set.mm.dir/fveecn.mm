include "cee.mm"
include "cfv.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wa.mm"
include "fveere.mm"
include "recnd.mm"

theorem fveecn
  let cA: class A
  let cI: class I
  let cN: class N


  assert |- ( ( A e. ( EE ` N ) /\ I e. ( 1 ... N ) ) -> ( A ` I ) e. CC )

  proof
    cA
    cN
    cee
    cfv
    wcel
    cI
    c1
    cN
    cfz
    co
    wcel
    wa
    cI
    cA
    cfv
    cA
    cI
    cN
    fveere
    recnd
end
