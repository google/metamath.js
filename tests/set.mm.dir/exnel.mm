include "wel.mm"
include "wn.mm"
include "wex.mm"
include "elirrv.mm"
include "nfth.mm"
include "weq.mm"
include "ax8.mm"
include "con3d.mm"
include "spime.mm"
include "ax-mp.mm"

theorem exnel
  let vx: setvar x
  let vy: setvar y


  assert |- E. x -. x e. y

  proof
    vy
    vy
    wel
    #
    wn
    #
    vx
    vy
    wel
    #
    wn
    #
    vx
    wex
    vy
    elirrv
    #
    @1
    @3
    vx
    vy
    @1
    vx
    @4
    nfth
    vx
    vy
    weq
    @2
    @0
    vx
    vy
    vy
    ax8
    con3d
    spime
    ax-mp
end
