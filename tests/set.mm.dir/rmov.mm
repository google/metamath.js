include "cvv.mm"
include "wrmo.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "df-rmo.mm"
include "vex.mm"
include "biantrur.mm"
include "mobii.mm"
include "bitr4i.mm"

theorem rmov
  let wph: wff ph
  let vx: setvar x


  assert |- ( E* x e. _V ph <-> E* x ph )

  proof
    wph
    vx
    cvv
    wrmo
    vx
    cv
    cvv
    wcel
    #
    wph
    wa
    #
    vx
    wmo
    wph
    vx
    wmo
    wph
    vx
    cvv
    df-rmo
    wph
    @1
    vx
    @0
    wph
    vx
    vex
    biantrur
    mobii
    bitr4i
end
