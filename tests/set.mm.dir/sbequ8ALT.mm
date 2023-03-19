include "wsb.mm"
include "weq.mm"
include "wi.mm"
include "equsb1.mm"
include "a1bi.mm"
include "sbim.mm"
include "bitr4i.mm"

theorem sbequ8ALT
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( [ y / x ] ph <-> [ y / x ] ( x = y -> ph ) )

  proof
    wph
    vx
    vy
    wsb
    #
    vx
    vy
    weq
    #
    vx
    vy
    wsb
    #
    @0
    wi
    @1
    wph
    wi
    vx
    vy
    wsb
    @2
    @0
    vx
    vy
    equsb1
    a1bi
    @1
    wph
    vx
    vy
    sbim
    bitr4i
end
