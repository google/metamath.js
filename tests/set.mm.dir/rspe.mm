include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wrex.mm"
include "19.8a.mm"
include "df-rex.mm"
include "sylibr.mm"

theorem rspe
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( ( x e. A /\ ph ) -> E. x e. A ph )

  proof
    vx
    cv
    cA
    wcel
    wph
    wa
    #
    @0
    vx
    wex
    wph
    vx
    cA
    wrex
    @0
    vx
    19.8a
    wph
    vx
    cA
    df-rex
    sylibr
end
