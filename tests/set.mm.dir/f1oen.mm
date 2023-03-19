include "cvv.mm"
include "wcel.mm"
include "wf1o.mm"
include "cen.mm"
include "wbr.mm"
include "f1oeng.mm"
include "mpan.mm"

theorem f1oen
  let cA: class A
  let cB: class B
  let cF: class F
  assume f1oen.1: |- A e. _V


  assert |- ( F : A -1-1-onto-> B -> A ~~ B )

  proof
    cA
    cvv
    wcel
    cA
    cB
    cF
    wf1o
    cA
    cB
    cen
    wbr
    f1oen.1
    cA
    cB
    cvv
    cF
    f1oeng
    mpan
end
