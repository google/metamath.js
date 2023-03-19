include "cafv.mm"
include "crn.mm"
include "wcel.mm"
include "afvelrn.mm"
include "funfni.mm"

theorem fnafvelrn
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F Fn A /\ B e. A ) -> ( F ''' B ) e. ran F )

  proof
    cB
    cF
    cafv
    cF
    crn
    wcel
    cA
    cB
    cF
    cB
    cF
    afvelrn
    funfni
end
