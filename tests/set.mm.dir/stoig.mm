include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctopon.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cts.mm"
include "cpr.mm"
include "ctps.mm"
include "toptopon.mm"
include "resttopon.mm"
include "sylanb.mm"
include "eqid.mm"
include "eltpsg.mm"
include "syl.mm"

theorem stoig
  let cA: class A
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cV: class V
  let cW: class W
  assume restuni.1: |- X = U. J


  assert |- ( ( J e. Top /\ A C_ X ) -> { <. ( Base ` ndx ) , A >. , <. ( TopSet ` ndx ) , ( J |`t A ) >. } e. TopSp )

  proof
    cJ
    ctop
    wcel
    #
    cA
    cX
    wss
    #
    wa
    cJ
    cA
    crest
    co
    #
    cA
    ctopon
    cfv
    wcel
    #
    cnx
    cbs
    cfv
    cA
    cop
    cnx
    cts
    cfv
    @2
    cop
    cpr
    #
    ctps
    wcel
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    @1
    @3
    cJ
    cX
    restuni.1
    toptopon
    cA
    cJ
    cX
    resttopon
    sylanb
    cA
    @2
    @4
    @4
    eqid
    eltpsg
    syl
end
