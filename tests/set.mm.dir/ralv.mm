include "cvv.mm"
include "wral.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "df-ral.mm"
include "vex.mm"
include "a1bi.mm"
include "albii.mm"
include "bitr4i.mm"

theorem ralv
  let wph: wff ph
  let vx: setvar x


  assert |- ( A. x e. _V ph <-> A. x ph )

  proof
    wph
    vx
    cvv
    wral
    vx
    cv
    cvv
    wcel
    #
    wph
    wi
    #
    vx
    wal
    wph
    vx
    wal
    wph
    vx
    cvv
    df-ral
    wph
    @1
    vx
    @0
    wph
    vx
    vex
    a1bi
    albii
    bitr4i
end
