include "cv.mm"
include "crab.mm"
include "wcel.mm"
include "rabid.mm"
include "simplbi.mm"

theorem rabidim1
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( x e. { x e. A | ph } -> x e. A )

  proof
    vx
    cv
    #
    wph
    vx
    cA
    crab
    wcel
    @0
    cA
    wcel
    wph
    wph
    vx
    cA
    rabid
    simplbi
end
