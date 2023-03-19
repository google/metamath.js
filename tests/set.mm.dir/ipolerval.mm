include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wa.mm"
include "copab.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cts.mm"
include "cordt.mm"
include "cple.mm"
include "coc.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "crab.mm"
include "cuni.mm"
include "cmpt.mm"
include "cun.mm"
include "cvv.mm"
include "cxp.mm"
include "simpl.mm"
include "vex.mm"
include "prss.mm"
include "sylibr.mm"
include "ssopab2i.mm"
include "df-xp.mm"
include "sseqtr4i.mm"
include "sqxpexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "c1.mm"
include "cdc.mm"
include "ipostr.mm"
include "pleid.mm"
include "csn.mm"
include "snsspr1.mm"
include "ssun2.mm"
include "sstri.mm"
include "strfv.mm"
include "syl.mm"
include "eqid.mm"
include "ipoval.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem ipolerval
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vo: setvar o
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume ipoval.i: |- I = ( toInc ` F )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint I x
  disjoint I y
  disjoint V x
  disjoint V y
  disjoint f o
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint o x
  disjoint o y
  disjoint F o
  disjoint .<_ f
  disjoint .<_ o
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( F e. V -> { <. x , y >. | ( { x , y } C_ F /\ x C_ y ) } = ( le ` I ) )

  proof
    cF
    cV
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cF
    wss
    #
    @1
    @2
    wss
    #
    wa
    #
    vx
    vy
    copab
    #
    cnx
    cbs
    cfv
    cF
    cop
    cnx
    cts
    cfv
    @6
    cordt
    cfv
    #
    cop
    cpr
    #
    cnx
    cple
    cfv
    @6
    cop
    #
    cnx
    coc
    cfv
    vx
    cF
    @2
    @1
    cin
    c0
    wceq
    vy
    cF
    crab
    cuni
    cmpt
    #
    cop
    #
    cpr
    #
    cun
    #
    cple
    cfv
    #
    cI
    cple
    cfv
    @0
    @6
    cvv
    wcel
    #
    @6
    @14
    wceq
    @0
    @6
    cF
    cF
    cxp
    #
    wss
    @16
    cvv
    wcel
    @15
    @6
    @1
    cF
    wcel
    @2
    cF
    wcel
    wa
    #
    vx
    vy
    copab
    @16
    @5
    @17
    vx
    vy
    @5
    @3
    @17
    @3
    @4
    simpl
    @1
    @2
    cF
    vx
    vex
    vy
    vex
    prss
    sylibr
    ssopab2i
    vx
    vy
    cF
    cF
    df-xp
    sseqtr4i
    cF
    cV
    sqxpexg
    @6
    @16
    cvv
    ssexg
    sylancr
    @6
    @13
    cple
    cvv
    c1
    c1
    c1
    cdc
    cop
    cF
    @7
    @6
    @10
    ipostr
    pleid
    @9
    csn
    @12
    @13
    @9
    @11
    snsspr1
    @12
    @8
    ssun2
    sstri
    strfv
    syl
    @0
    cI
    @13
    cple
    vx
    vy
    cF
    cI
    @6
    cV
    ipoval.i
    @6
    eqid
    ipoval
    fveq2d
    eqtr4d
end
