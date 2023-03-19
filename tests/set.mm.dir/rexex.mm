include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "exsimpr.mm"
include "sylbi.mm"

theorem rexex
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E. x e. A ph -> E. x ph )

  proof
    wph
    vx
    cA
    wrex
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    vx
    wex
    wph
    vx
    wex
    wph
    vx
    cA
    df-rex
    @0
    wph
    vx
    exsimpr
    sylbi
end
