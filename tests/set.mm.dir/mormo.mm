include "wmo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wrmo.mm"
include "moan.mm"
include "df-rmo.mm"
include "sylibr.mm"

theorem mormo
  let wph: wff ph
  let vx: setvar x
  let cA: class A


  assert |- ( E* x ph -> E* x e. A ph )

  proof
    wph
    vx
    wmo
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    vx
    wmo
    wph
    vx
    cA
    wrmo
    wph
    @0
    vx
    moan
    wph
    vx
    cA
    df-rmo
    sylibr
end
