include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "copab.mm"
include "opex.mm"
include "copsexg.mm"
include "bicomd.mm"
include "df-opab.mm"
include "elab2.mm"

theorem opabid
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( <. x , y >. e. { <. x , y >. | ph } <-> ph )

  proof
    vz
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    vy
    wex
    vx
    wex
    #
    wph
    vz
    @3
    wph
    vx
    vy
    copab
    @1
    @2
    opex
    @4
    wph
    @5
    wph
    vx
    vy
    @0
    copsexg
    bicomd
    wph
    vx
    vy
    vz
    df-opab
    elab2
end
