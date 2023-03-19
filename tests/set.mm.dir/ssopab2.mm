include "wi.mm"
include "wal.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "copab.mm"
include "id.mm"
include "anim2d.mm"
include "aleximi.mm"
include "ss2abdv.mm"
include "df-opab.mm"
include "3sstr4g.mm"

theorem ssopab2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A. x A. y ( ph -> ps ) -> { <. x , y >. | ph } C_ { <. x , y >. | ps } )

  proof
    wph
    wps
    wi
    #
    vy
    wal
    #
    vx
    wal
    #
    vz
    cv
    vx
    cv
    vy
    cv
    cop
    wceq
    #
    wph
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    @3
    wps
    wa
    #
    vy
    wex
    #
    vx
    wex
    #
    vz
    cab
    wph
    vx
    vy
    copab
    wps
    vx
    vy
    copab
    @2
    @6
    @9
    vz
    @1
    @5
    @8
    vx
    @0
    @4
    @7
    vy
    @0
    wph
    wps
    @3
    @0
    id
    anim2d
    aleximi
    aleximi
    ss2abdv
    wph
    vx
    vy
    vz
    df-opab
    wps
    vx
    vy
    vz
    df-opab
    3sstr4g
end
