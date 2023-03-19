include "wcel.mm"
include "ce1.mm"
include "cfv.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cevl.mm"
include "ces1.mm"
include "eqid.mm"
include "evl1fval.mm"
include "wceq.mm"
include "a1i.mm"
include "ces.mm"
include "cpw.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "pwid.mm"
include "evls1fval.mm"
include "mpan2.mm"
include "evlval.mm"
include "eqcomi.mm"
include "coeq2i.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"

theorem evl1fval1lem
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume evl1fval1.q: |- Q = ( eval1 ` R )
  assume evl1fval1.b: |- B = ( Base ` R )


  assert |- ( R e. V -> Q = ( R evalSub1 B ) )

  proof
    cR
    cV
    wcel
    #
    cR
    ce1
    cfv
    #
    vx
    cB
    cB
    c1o
    cmap
    co
    cmap
    co
    vx
    cv
    vy
    cB
    c1o
    vy
    cv
    csn
    cxp
    cmpt
    ccom
    cmpt
    #
    c1o
    cR
    cevl
    co
    #
    ccom
    #
    cQ
    cR
    cB
    ces1
    co
    #
    vx
    vy
    cB
    @3
    cR
    @1
    @1
    eqid
    @3
    eqid
    #
    evl1fval1.b
    evl1fval
    cQ
    @1
    wceq
    @0
    evl1fval1.q
    a1i
    @0
    @5
    @2
    cB
    c1o
    cR
    ces
    co
    #
    cfv
    #
    ccom
    #
    @4
    @0
    cB
    cB
    cpw
    wcel
    @5
    @9
    wceq
    cB
    cB
    cR
    cbs
    cfv
    cvv
    evl1fval1.b
    cR
    cbs
    fvex
    eqeltri
    pwid
    vx
    vy
    cB
    @5
    cB
    cR
    @7
    cV
    @5
    eqid
    @7
    eqid
    evl1fval1.b
    evls1fval
    mpan2
    @8
    @3
    @2
    @3
    @8
    cB
    @3
    cR
    c1o
    @6
    evl1fval1.b
    evlval
    eqcomi
    coeq2i
    syl6eq
    3eqtr4a
end
