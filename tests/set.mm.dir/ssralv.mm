include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "ssel.mm"
include "imim1d.mm"
include "ralimdv2.mm"

theorem ssralv
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A C_ B -> ( A. x e. B ph -> A. x e. A ph ) )

  proof
    cA
    cB
    wss
    #
    wph
    wph
    vx
    cB
    cA
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
    imim1d
    ralimdv2
end
