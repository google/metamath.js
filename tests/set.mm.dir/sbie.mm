include "wb.mm"
include "wsb.mm"
include "weq.mm"
include "equsb1.mm"
include "sbimi.mm"
include "ax-mp.mm"
include "sbf.mm"
include "sblbis.mm"
include "mpbi.mm"

theorem sbie
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume sbie.1: |- F/ x ps
  assume sbie.2: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( [ y / x ] ph <-> ps )

  proof
    wph
    wps
    wb
    #
    vx
    vy
    wsb
    #
    wph
    vx
    vy
    wsb
    wps
    wb
    vx
    vy
    weq
    #
    vx
    vy
    wsb
    @1
    vx
    vy
    equsb1
    @2
    @0
    vx
    vy
    sbie.2
    sbimi
    ax-mp
    wps
    wps
    wph
    vx
    vy
    wps
    vx
    vy
    sbie.1
    sbf
    sblbis
    mpbi
end
