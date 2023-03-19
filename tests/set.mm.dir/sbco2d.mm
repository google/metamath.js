include "wsb.mm"
include "wi.mm"
include "nfim1.mm"
include "sbco2.mm"
include "sbrim.mm"
include "sbbii.mm"
include "bitri.mm"
include "3bitr3i.mm"
include "pm5.74ri.mm"

theorem sbco2d
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sbco2d.1: |- F/ x ph
  assume sbco2d.2: |- F/ z ph
  assume sbco2d.3: |- ( ph -> F/ z ps )


  assert |- ( ph -> ( [ y / z ] [ z / x ] ps <-> [ y / x ] ps ) )

  proof
    wph
    wps
    vx
    vz
    wsb
    #
    vz
    vy
    wsb
    #
    wps
    vx
    vy
    wsb
    #
    wph
    wps
    wi
    #
    vx
    vz
    wsb
    #
    vz
    vy
    wsb
    #
    @3
    vx
    vy
    wsb
    wph
    @1
    wi
    #
    wph
    @2
    wi
    @3
    vx
    vy
    vz
    wph
    wps
    vz
    sbco2d.2
    sbco2d.3
    nfim1
    sbco2
    @5
    wph
    @0
    wi
    #
    vz
    vy
    wsb
    @6
    @4
    @7
    vz
    vy
    wph
    wps
    vx
    vz
    sbco2d.1
    sbrim
    sbbii
    wph
    @0
    vz
    vy
    sbco2d.2
    sbrim
    bitri
    wph
    wps
    vx
    vy
    sbco2d.1
    sbrim
    3bitr3i
    pm5.74ri
end
