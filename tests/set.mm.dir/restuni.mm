include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "ctopon.mm"
include "cfv.mm"
include "cuni.mm"
include "wceq.mm"
include "toptopon.mm"
include "resttopon.mm"
include "sylanb.mm"
include "toponuni.mm"
include "syl.mm"

theorem restuni
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


  assert |- ( ( J e. Top /\ A C_ X ) -> A = U. ( J |`t A ) )

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
    cA
    @2
    cuni
    wceq
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
    toponuni
    syl
end
