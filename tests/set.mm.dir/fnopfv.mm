include "cfv.mm"
include "cop.mm"
include "wcel.mm"
include "funfvop.mm"
include "funfni.mm"

theorem fnopfv
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F Fn A /\ B e. A ) -> <. B , ( F ` B ) >. e. F )

  proof
    cB
    cB
    cF
    cfv
    cop
    cF
    wcel
    cA
    cB
    cF
    cB
    cF
    funfvop
    funfni
end
