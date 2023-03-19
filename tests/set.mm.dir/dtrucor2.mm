include "weq.mm"
include "wex.mm"
include "wn.mm"
include "wa.mm"
include "ax6e.mm"
include "wi.mm"
include "cv.mm"
include "necon2bi.mm"
include "pm2.01.mm"
include "ax-mp.mm"
include "nex.mm"
include "pm2.24ii.mm"

theorem dtrucor2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  assume dtrucor2.1: |- ( x = y -> x =/= y )


  assert |- ( ph /\ -. ph )

  proof
    vx
    vy
    weq
    #
    vx
    wex
    wph
    wph
    wn
    wa
    vx
    vy
    ax6e
    @0
    vx
    @0
    @0
    wn
    #
    wi
    @1
    @0
    vx
    cv
    vy
    cv
    dtrucor2.1
    necon2bi
    @0
    pm2.01
    ax-mp
    nex
    pm2.24ii
end
