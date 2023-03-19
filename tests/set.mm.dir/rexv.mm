include "cvv.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "df-rex.mm"
include "vex.mm"
include "biantrur.mm"
include "exbii.mm"
include "bitr4i.mm"

theorem rexv
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x e. _V ph <-> E. x ph )

  proof
    wph
    vx
    cvv
    wrex
    vx
    cv
    cvv
    wcel
    #
    wph
    wa
    #
    vx
    wex
    wph
    vx
    wex
    wph
    vx
    cvv
    df-rex
    wph
    @1
    vx
    @0
    wph
    vx
    vex
    biantrur
    exbii
    bitr4i
end
