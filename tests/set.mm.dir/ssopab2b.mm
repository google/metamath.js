include "copab.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "nfopab1.mm"
include "nfss.mm"
include "nfopab2.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "ssel.mm"
include "opabid.mm"
include "3imtr3g.mm"
include "alrimi.mm"
include "ssopab2.mm"
include "impbii.mm"

theorem ssopab2b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( { <. x , y >. | ph } C_ { <. x , y >. | ps } <-> A. x A. y ( ph -> ps ) )

  proof
    wph
    vx
    vy
    copab
    #
    wps
    vx
    vy
    copab
    #
    wss
    #
    wph
    wps
    wi
    #
    vy
    wal
    #
    vx
    wal
    @2
    @4
    vx
    vx
    @0
    @1
    wph
    vx
    vy
    nfopab1
    wps
    vx
    vy
    nfopab1
    nfss
    @2
    @3
    vy
    vy
    @0
    @1
    wph
    vx
    vy
    nfopab2
    wps
    vx
    vy
    nfopab2
    nfss
    @2
    vx
    cv
    vy
    cv
    cop
    #
    @0
    wcel
    @5
    @1
    wcel
    wph
    wps
    @0
    @1
    @5
    ssel
    wph
    vx
    vy
    opabid
    wps
    vx
    vy
    opabid
    3imtr3g
    alrimi
    alrimi
    wph
    wps
    vx
    vy
    ssopab2
    impbii
end
