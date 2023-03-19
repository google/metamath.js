include "wi.mm"
include "wsb.mm"
include "wnf.mm"
include "sbim.mm"
include "sbft.mm"
include "imbi1d.mm"
include "syl5bb.mm"

theorem wl-sbrimt
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y


  assert |- ( F/ x ph -> ( [ y / x ] ( ph -> ps ) <-> ( ph -> [ y / x ] ps ) ) )

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
    vx
    wnf
    #
    wph
    @1
    wi
    wph
    wps
    vx
    vy
    sbim
    @2
    @0
    wph
    @1
    wph
    vx
    vy
    sbft
    imbi1d
    syl5bb
end
