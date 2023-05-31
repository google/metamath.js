include "weq.mm"
include "wn.mm"
include "wi.mm"
include "ax-1.mm"
include "equeuclr.mm"
include "con3rr3.mm"
include "imim1d.mm"
include "pm2.43.mm"
include "syl6.mm"
include "impbid2.mm"
include "pm5.74i.mm"

theorem ax13b
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y
  param vz: setvar z


  assert |- ( ( -. x = y -> ( y = z -> ph ) ) <-> ( -. x = y -> ( -. x = z -> ( y = z -> ph ) ) ) )

  proof
    vx
    vy
    weq
    #
    wn
    #
    vy
    vz
    weq
    #
    wph
    wi
    #
    vx
    vz
    weq
    #
    wn
    #
    @3
    wi
    #
    @1
    @3
    @6
    @3
    @5
    ax-1
    @1
    @6
    @2
    @3
    wi
    @3
    @1
    @2
    @5
    @3
    @2
    @4
    @0
    vy
    vx
    vz
    equeuclr
    con3rr3
    imim1d
    @2
    wph
    pm2.43
    syl6
    impbid2
    pm5.74i
end
