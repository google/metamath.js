include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "ssel.mm"
include "anim1d.mm"
include "reximdv2.mm"

theorem ssrexv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B -> ( E. x e. A ph -> E. x e. B ph ) )

  proof
    cA
    cB
    wss
    #
    wph
    wph
    vx
    cA
    cB
    @0
    vx
    cv
    #
    cA
    wcel
    @1
    cB
    wcel
    wph
    cA
    cB
    @1
    ssel
    anim1d
    reximdv2
end
