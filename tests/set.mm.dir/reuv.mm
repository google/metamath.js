include "cvv.mm"
include "wreu.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "weu.mm"
include "df-reu.mm"
include "vex.mm"
include "biantrur.mm"
include "eubii.mm"
include "bitr4i.mm"

theorem reuv
  let wph: wff ph
  let vx: setvar x


  assert |- ( E! x e. _V ph <-> E! x ph )

  proof
    wph
    vx
    cvv
    wreu
    vx
    cv
    cvv
    wcel
    #
    wph
    wa
    #
    vx
    weu
    wph
    vx
    weu
    wph
    vx
    cvv
    df-reu
    wph
    @1
    vx
    @0
    wph
    vx
    vex
    biantrur
    eubii
    bitr4i
end
