include "c0.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "wne.mm"
include "wn.mm"
include "vex.mm"
include "opnzi.mm"
include "simpl.mm"
include "eqcomd.mm"
include "necon3ai.mm"
include "ax-mp.mm"
include "nex.mm"
include "elxp.mm"
include "mtbir.mm"

theorem 0nelxpOLD
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- -. (/) e. ( A X. B )

  proof
    c0
    cA
    cB
    cxp
    wcel
    c0
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @0
    cA
    wcel
    @1
    cB
    wcel
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    @6
    vx
    @5
    vy
    @2
    c0
    wne
    @5
    wn
    @0
    @1
    vx
    vex
    vy
    vex
    opnzi
    @5
    @2
    c0
    @5
    c0
    @2
    @3
    @4
    simpl
    eqcomd
    necon3ai
    ax-mp
    nex
    nex
    vx
    vy
    c0
    cA
    cB
    elxp
    mtbir
end
