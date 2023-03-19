include "coprab.mm"
include "wss.mm"
include "wi.mm"
include "wal.mm"
include "nfoprab1.mm"
include "nfss.mm"
include "nfoprab2.mm"
include "nfoprab3.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "ssel.mm"
include "oprabid.mm"
include "3imtr3g.mm"
include "alrimi.mm"
include "ssoprab2.mm"
include "impbii.mm"

theorem ssoprab2b
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( { <. <. x , y >. , z >. | ph } C_ { <. <. x , y >. , z >. | ps } <-> A. x A. y A. z ( ph -> ps ) )

  proof
    wph
    vx
    vy
    vz
    coprab
    #
    wps
    vx
    vy
    vz
    coprab
    #
    wss
    #
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
    @2
    @5
    vx
    vx
    @0
    @1
    wph
    vx
    vy
    vz
    nfoprab1
    wps
    vx
    vy
    vz
    nfoprab1
    nfss
    @2
    @4
    vy
    vy
    @0
    @1
    wph
    vx
    vy
    vz
    nfoprab2
    wps
    vx
    vy
    vz
    nfoprab2
    nfss
    @2
    @3
    vz
    vz
    @0
    @1
    wph
    vx
    vy
    vz
    nfoprab3
    wps
    vx
    vy
    vz
    nfoprab3
    nfss
    @2
    vx
    cv
    vy
    cv
    cop
    vz
    cv
    cop
    #
    @0
    wcel
    @6
    @1
    wcel
    wph
    wps
    @0
    @1
    @6
    ssel
    wph
    vx
    vy
    vz
    oprabid
    wps
    vx
    vy
    vz
    oprabid
    3imtr3g
    alrimi
    alrimi
    alrimi
    wph
    wps
    vx
    vy
    vz
    ssoprab2
    impbii
end
