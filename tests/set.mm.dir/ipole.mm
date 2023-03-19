include "wcel.mm"
include "w3a.mm"
include "cv.mm"
include "cpr.mm"
include "wss.mm"
include "wa.mm"
include "copab.mm"
include "wbr.mm"
include "wb.mm"
include "wceq.mm"
include "preq12.mm"
include "sseq1d.mm"
include "sseq12.mm"
include "anbi12d.mm"
include "eqid.mm"
include "brabga.mm"
include "3adant1.mm"
include "cple.mm"
include "cfv.mm"
include "ipolerval.mm"
include "syl6reqr.mm"
include "breqd.mm"
include "3ad2ant1.mm"
include "prssi.mm"
include "biantrurd.mm"
include "3bitr4d.mm"

theorem ipole
  let cF: class F
  let cI: class I
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vo: setvar o
  let vx: setvar x
  let vy: setvar y
  assume ipoval.i: |- I = ( toInc ` F )
  assume ipole.l: |- .<_ = ( le ` I )


  assert |- ( ( F e. V /\ X e. F /\ Y e. F ) -> ( X .<_ Y <-> X C_ Y ) )

  proof
    cF
    cV
    wcel
    #
    cX
    cF
    wcel
    #
    cY
    cF
    wcel
    #
    w3a
    #
    cX
    cY
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cF
    wss
    #
    @4
    @5
    wss
    #
    wa
    #
    vx
    vy
    copab
    #
    wbr
    #
    cX
    cY
    cpr
    #
    cF
    wss
    #
    cX
    cY
    wss
    #
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    @14
    @1
    @2
    @11
    @15
    wb
    @0
    @9
    @15
    vx
    vy
    cX
    cY
    @10
    cF
    cF
    @4
    cX
    wceq
    @5
    cY
    wceq
    wa
    #
    @7
    @13
    @8
    @14
    @17
    @6
    @12
    cF
    @4
    @5
    cX
    cY
    preq12
    sseq1d
    @4
    cX
    @5
    cY
    sseq12
    anbi12d
    @10
    eqid
    brabga
    3adant1
    @0
    @1
    @16
    @11
    wb
    @2
    @0
    c.le
    @10
    cX
    cY
    @0
    @10
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
    breqd
    3ad2ant1
    @3
    @13
    @14
    @1
    @2
    @13
    @0
    cX
    cY
    cF
    prssi
    3adant1
    biantrurd
    3bitr4d
end
