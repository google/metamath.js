include "cab.mm"
include "wsb.mm"
include "cv.mm"
include "wcel.mm"
include "sbco2.mm"
include "sbie.mm"
include "sbbii.mm"
include "bitr3i.mm"
include "df-clab.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem cbvab
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cbvab.1: |- F/ y ph
  assume cbvab.2: |- F/ x ps
  assume cbvab.3: |- ( x = y -> ( ph <-> ps ) )


  assert |- { x | ph } = { y | ps }

  proof
    vz
    wph
    vx
    cab
    #
    wps
    vy
    cab
    #
    wph
    vx
    vz
    wsb
    #
    wps
    vy
    vz
    wsb
    #
    vz
    cv
    #
    @0
    wcel
    @4
    @1
    wcel
    @2
    wph
    vx
    vy
    wsb
    #
    vy
    vz
    wsb
    @3
    wph
    vx
    vz
    vy
    cbvab.1
    sbco2
    @5
    wps
    vy
    vz
    wph
    wps
    vx
    vy
    cbvab.2
    cbvab.3
    sbie
    sbbii
    bitr3i
    wph
    vz
    vx
    df-clab
    wps
    vz
    vy
    df-clab
    3bitr4i
    eqriv
end
