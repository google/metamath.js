include "cvv.mm"
include "wcel.mm"
include "c0.mm"
include "cid.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "fvi.mm"
include "preq2d.mm"
include "wn.mm"
include "csn.mm"
include "dfsn2.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "prprc2.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem indislem
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let cV: class V


  assert |- { (/) , ( _I ` A ) } = { (/) , A }

  proof
    cA
    cvv
    wcel
    #
    c0
    cA
    cid
    cfv
    #
    cpr
    #
    c0
    cA
    cpr
    #
    wceq
    @0
    @1
    cA
    c0
    cA
    cvv
    fvi
    preq2d
    @0
    wn
    #
    c0
    c0
    cpr
    #
    c0
    csn
    #
    @2
    @3
    @6
    @5
    c0
    dfsn2
    eqcomi
    @4
    @1
    c0
    c0
    cA
    cid
    fvprc
    preq2d
    c0
    cA
    prprc2
    3eqtr4a
    pm2.61i
end
