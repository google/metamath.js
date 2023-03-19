include "wi.mm"
include "wsb.mm"
include "sbim.mm"
include "sbf.mm"
include "imbi2i.mm"
include "bitri.mm"

theorem sblim
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume sblim.1: |- F/ x ps


  assert |- ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) )

  proof
    wph
    wps
    wi
    vx
    vy
    wsb
    wph
    vx
    vy
    wsb
    #
    wps
    vx
    vy
    wsb
    #
    wi
    @0
    wps
    wi
    wph
    wps
    vx
    vy
    sbim
    @1
    wps
    @0
    wps
    vx
    vy
    sblim.1
    sbf
    imbi2i
    bitri
end
