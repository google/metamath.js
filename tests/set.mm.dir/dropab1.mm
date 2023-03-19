include "cv.mm"
include "wceq.mm"
include "wal.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "opeq1.mm"
include "sps.mm"
include "eqeq2d.mm"
include "anbi1d.mm"
include "drex2.mm"
include "drex1.mm"
include "abbidv.mm"
include "df-opab.mm"
include "3eqtr4g.mm"

theorem dropab1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( A. x x = y -> { <. x , z >. | ph } = { <. y , z >. | ph } )

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
    @0
    vz
    cv
    #
    cop
    #
    wceq
    #
    wph
    wa
    #
    vz
    wex
    #
    vx
    wex
    #
    vw
    cab
    @4
    @1
    @5
    cop
    #
    wceq
    #
    wph
    wa
    #
    vz
    wex
    #
    vy
    wex
    #
    vw
    cab
    wph
    vx
    vz
    copab
    wph
    vy
    vz
    copab
    @3
    @10
    @15
    vw
    @9
    @14
    vx
    vy
    @8
    @13
    vx
    vy
    vz
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
    opeq1
    sps
    eqeq2d
    anbi1d
    drex2
    drex1
    abbidv
    wph
    vx
    vz
    vw
    df-opab
    wph
    vy
    vz
    vw
    df-opab
    3eqtr4g
end
