include "wcel.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wa.mm"
include "copab.mm"
include "cordt.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cts.mm"
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
include "fvex.mm"
include "c1.mm"
include "cdc.mm"
include "ipostr.mm"
include "tsetid.mm"
include "csn.mm"
include "snsspr2.mm"
include "ssun1.mm"
include "sstri.mm"
include "strfv.mm"
include "ax-mp.mm"
include "ipolerval.mm"
include "syl6reqr.mm"
include "fveq2d.mm"
include "eqid.mm"
include "ipoval.mm"
include "3eqtr4a.mm"

theorem ipotset
  let cF: class F
  let cI: class I
  let c.le: class .<_
  let cV: class V
  let vf: setvar f
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let cX: class X
  let cY: class Y
  assume ipoval.i: |- I = ( toInc ` F )
  assume ipole.l: |- .<_ = ( le ` I )


  assert |- ( F e. V -> ( ordTop ` .<_ ) = ( TopSet ` I ) )

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
    @1
    @2
    wss
    wa
    vx
    vy
    copab
    #
    cordt
    cfv
    #
    cnx
    cbs
    cfv
    cF
    cop
    #
    cnx
    cts
    cfv
    @4
    cop
    #
    cpr
    #
    cnx
    cple
    cfv
    @3
    cop
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
    cpr
    #
    cun
    #
    cts
    cfv
    #
    c.le
    cordt
    cfv
    cI
    cts
    cfv
    @4
    cvv
    wcel
    @4
    @11
    wceq
    @3
    cordt
    fvex
    @4
    @10
    cts
    cvv
    c1
    c1
    c1
    cdc
    cop
    cF
    @4
    @3
    @8
    ipostr
    tsetid
    @6
    csn
    @7
    @10
    @5
    @6
    snsspr2
    @7
    @9
    ssun1
    sstri
    strfv
    ax-mp
    @0
    c.le
    @3
    cordt
    @0
    @3
    cI
    cple
    cfv
    c.le
    vx
    vy
    cF
    cI
    cV
    ipoval.i
    ipolerval
    ipole.l
    syl6reqr
    fveq2d
    @0
    cI
    @10
    cts
    vx
    vy
    cF
    cI
    @3
    cV
    ipoval.i
    @3
    eqid
    ipoval
    fveq2d
    3eqtr4a
end
