include "weq.mm"
include "wsb.mm"
include "sbequi.mm"
include "wi.mm"
include "equcoms.mm"
include "impbid.mm"

theorem sbequ
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z


  assert |- ( x = y -> ( [ x / z ] ph <-> [ y / z ] ph ) )

  proof
    vx
    vy
    weq
    wph
    vz
    vx
    wsb
    #
    wph
    vz
    vy
    wsb
    #
    wph
    vx
    vy
    vz
    sbequi
    @1
    @0
    wi
    vy
    vx
    wph
    vy
    vx
    vz
    sbequi
    equcoms
    impbid
end
