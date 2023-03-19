include "wi.mm"
include "wal.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "coprab.mm"
include "id.mm"
include "anim2d.mm"
include "aleximi.mm"
include "ss2abdv.mm"
include "df-oprab.mm"
include "3sstr4g.mm"

theorem ssoprab2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( A. x A. y A. z ( ph -> ps ) -> { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps } )

  proof
    wph
    wps
    wi
    #
    vz
    wal
    #
    vy
    wal
    #
    vx
    wal
    #
    vw
    cv
    vx
    cv
    vy
    cv
    cop
    vz
    cv
    cop
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
    vx
    wex
    #
    vw
    cab
    @4
    wps
    wa
    #
    vz
    wex
    #
    vy
    wex
    #
    vx
    wex
    #
    vw
    cab
    wph
    vx
    vy
    vz
    coprab
    wps
    vx
    vy
    vz
    coprab
    @3
    @8
    @12
    vw
    @2
    @7
    @11
    vx
    @1
    @6
    @10
    vy
    @0
    @5
    @9
    vz
    @0
    wph
    wps
    @4
    @0
    id
    anim2d
    aleximi
    aleximi
    aleximi
    ss2abdv
    wph
    vx
    vy
    vz
    vw
    df-oprab
    wps
    vx
    vy
    vz
    vw
    df-oprab
    3sstr4g
end
