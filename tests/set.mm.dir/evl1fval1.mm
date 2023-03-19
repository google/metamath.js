include "cvv.mm"
include "wcel.mm"
include "ces1.mm"
include "co.mm"
include "wceq.mm"
include "evl1fval1lem.mm"
include "wn.mm"
include "c0.mm"
include "ce1.mm"
include "cfv.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "reldmevls1.mm"
include "ovprc1.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem evl1fval1
  let cB: class B
  let cQ: class Q
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  assume evl1fval1.q: |- Q = ( eval1 ` R )
  assume evl1fval1.b: |- B = ( Base ` R )


  assert |- Q = ( R evalSub1 B )

  proof
    cR
    cvv
    wcel
    #
    cQ
    cR
    cB
    ces1
    co
    #
    wceq
    cB
    cQ
    cR
    cvv
    evl1fval1.q
    evl1fval1.b
    evl1fval1lem
    @0
    wn
    #
    cQ
    c0
    @1
    @2
    cQ
    cR
    ce1
    cfv
    c0
    evl1fval1.q
    cR
    ce1
    fvprc
    syl5eq
    cR
    cB
    ces1
    reldmevls1
    ovprc1
    eqtr4d
    pm2.61i
end
