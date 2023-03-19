include "cfv.mm"
include "crn.mm"
include "wcel.mm"
include "fvelrn.mm"
include "funfni.mm"

theorem fnfvelrn
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( ( F Fn A /\ B e. A ) -> ( F ` B ) e. ran F )

  proof
    cB
    cF
    cfv
    cF
    crn
    wcel
    cA
    cB
    cF
    cB
    cF
    fvelrn
    funfni
end
