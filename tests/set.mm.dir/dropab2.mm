include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "opeq2.mm"
include "sps.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "drex1.mm"
include "drex2.mm"
include "abbidv.mm"
include "df-opab.mm"
include "3eqtr4g.mm"

theorem dropab2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( A. x x = y -> { <. z , x >. | ph } = { <. z , y >. | ph } )

  proof
    vx
    cv
    #
    vy
    cv
    #
    wceq
    #
    vx
    wal
    #
    vw
    cv
    #
    vz
    cv
    #
    @0
    cop
    #
    wceq
    #
    wph
    wa
    #
    vx
    wex
    #
    vz
    wex
    #
    vw
    cab
    @4
    @5
    @1
    cop
    #
    wceq
    #
    wph
    wa
    #
    vy
    wex
    #
    vz
    wex
    #
    vw
    cab
    wph
    vz
    vx
    copab
    wph
    vz
    vy
    copab
    @3
    @10
    @15
    vw
    @9
    @14
    vx
    vy
    vz
    @8
    @13
    vx
    vy
    @3
    @7
    @12
    wph
    @3
    @6
    @11
    @4
    @2
    @6
    @11
    wceq
    vx
    @0
    @1
    @5
    opeq2
    sps
    eqeq2d
    anbi1d
    drex1
    drex2
    abbidv
    wph
    vz
    vx
    vw
    df-opab
    wph
    vz
    vy
    vw
    df-opab
    3eqtr4g
end
