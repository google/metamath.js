include "wcel.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cts.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wa.mm"
include "copab.mm"
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
include "c1.mm"
include "cdc.mm"
include "ipostr.mm"
include "baseid.mm"
include "csn.mm"
include "snsspr1.mm"
include "ssun1.mm"
include "sstri.mm"
include "strfv.mm"
include "eqid.mm"
include "ipoval.mm"
include "fveq2d.mm"
include "eqtr4d.mm"

theorem ipobas
  let cF: class F
  let cI: class I
  let cV: class V
  let vf: setvar f
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume ipoval.i: |- I = ( toInc ` F )


  assert |- ( F e. V -> F = ( Base ` I ) )

  proof
    cF
    cV
    wcel
    #
    cF
    cnx
    cbs
    cfv
    cF
    cop
    #
    cnx
    cts
    cfv
    vx
    cv
    #
    vy
    cv
    #
    cpr
    cF
    wss
    @2
    @3
    wss
    wa
    vx
    vy
    copab
    #
    cordt
    cfv
    #
    cop
    #
    cpr
    #
    cnx
    cple
    cfv
    @4
    cop
    cnx
    coc
    cfv
    vx
    cF
    @3
    @2
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
    cbs
    cfv
    cI
    cbs
    cfv
    cF
    @10
    cbs
    cV
    c1
    c1
    c1
    cdc
    cop
    cF
    @5
    @4
    @8
    ipostr
    baseid
    @1
    csn
    @7
    @10
    @1
    @6
    snsspr1
    @7
    @9
    ssun1
    sstri
    strfv
    @0
    cI
    @10
    cbs
    vx
    vy
    cF
    cI
    @4
    cV
    ipoval.i
    @4
    eqid
    ipoval
    fveq2d
    eqtr4d
end
