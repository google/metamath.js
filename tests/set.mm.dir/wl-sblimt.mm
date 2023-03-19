include "wi.mm"
include "wsb.mm"
include "wnf.mm"
include "sbim.mm"
include "sbft.mm"
include "imbi2d.mm"
include "syl5bb.mm"

theorem wl-sblimt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( F/ x ps -> ( [ y / x ] ( ph -> ps ) <-> ( [ y / x ] ph -> ps ) ) )

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
    wps
    vx
    wnf
    #
    @0
    wps
    wi
    wph
    wps
    vx
    vy
    sbim
    @2
    @1
    wps
    @0
    wps
    vx
    vy
    sbft
    imbi2d
    syl5bb
end
