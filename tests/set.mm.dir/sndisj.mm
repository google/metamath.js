include "cv.mm"
include "csn.mm"
include "wdisj.mm"
include "wcel.mm"
include "wa.mm"
include "wmo.mm"
include "dfdisj2.mm"
include "weq.mm"
include "moeq.mm"
include "simpr.mm"
include "velsn.mm"
include "sylib.mm"
include "equcomd.mm"
include "moimi.mm"
include "ax-mp.mm"
include "mpgbir.mm"

theorem sndisj
  let vx: setvar x
  let cA: class A
  let vy: setvar y


  assert |- Disj_ x e. A { x }

  proof
    vx
    cA
    vx
    cv
    #
    csn
    #
    wdisj
    @0
    cA
    wcel
    #
    vy
    cv
    #
    @1
    wcel
    #
    wa
    #
    vx
    wmo
    #
    vy
    vx
    vy
    cA
    @1
    dfdisj2
    vx
    vy
    weq
    #
    vx
    wmo
    @6
    vx
    @3
    moeq
    @5
    @7
    vx
    @5
    vy
    vx
    @5
    @4
    vy
    vx
    weq
    @2
    @4
    simpr
    vy
    @0
    velsn
    sylib
    equcomd
    moimi
    ax-mp
    mpgbir
end
