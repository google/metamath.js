include "wi.mm"
include "wsb.mm"
include "sbim.mm"
include "sbf.mm"
include "imbi1i.mm"
include "bitri.mm"

theorem sbrim
  param wph: wff ph
  param wps: wff ps
  param vx: setvar x
  param vy: setvar y
  assume sbrim.1: |- F/ x ph


  assert |- ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) )

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
    wph
    @1
    wi
    wph
    wps
    vx
    vy
    sbim
    @0
    wph
    @1
    wph
    vx
    vy
    sbrim.1
    sbf
    imbi1i
    bitri
end
