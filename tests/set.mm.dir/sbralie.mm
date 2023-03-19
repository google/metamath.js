include "cv.mm"
include "wral.mm"
include "wsb.mm"
include "cbvralsv.mm"
include "sbbii.mm"
include "nfv.mm"
include "raleq.mm"
include "sbie.mm"
include "bitri.mm"
include "sbco2.mm"
include "ralbii.mm"

theorem sbralie
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sbralie.1: |- ( x = y -> ( ph <-> ps ) )

  disjoint x y
  disjoint ph y
  disjoint ps x
  disjoint x z
  disjoint y z
  disjoint ph z
  disjoint ps z
  assert |- ( [ x / y ] A. x e. y ph <-> A. y e. x ps )

  proof
    wph
    vx
    vy
    cv
    #
    wral
    #
    vy
    vx
    wsb
    #
    wph
    vx
    vz
    wsb
    #
    vz
    vx
    cv
    #
    wral
    #
    wps
    vy
    @4
    wral
    #
    @2
    @3
    vz
    @0
    wral
    #
    vy
    vx
    wsb
    @5
    @1
    @7
    vy
    vx
    wph
    vx
    vz
    @0
    cbvralsv
    sbbii
    @7
    @5
    vy
    vx
    @5
    vy
    nfv
    @3
    vz
    @0
    @4
    raleq
    sbie
    bitri
    @5
    @3
    vz
    vy
    wsb
    #
    vy
    @4
    wral
    @6
    @3
    vz
    vy
    @4
    cbvralsv
    @8
    wps
    vy
    @4
    @8
    wph
    vx
    vy
    wsb
    wps
    wph
    vx
    vy
    vz
    wph
    vz
    nfv
    sbco2
    wph
    wps
    vx
    vy
    wps
    vx
    nfv
    sbralie.1
    sbie
    bitri
    ralbii
    bitri
    bitri
end
