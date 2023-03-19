include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "cpr.mm"
include "cglb.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "eqid.mm"
include "simp1l.mm"
include "simp2l.mm"
include "simp2r.mm"
include "meetval.mm"
include "fveq2d.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "simp1.mm"
include "prssi.mm"
include "3ad2ant2.mm"
include "prnzg.mm"
include "syl.mm"
include "simp3.mm"
include "breq1d.mm"
include "mtbid.mm"
include "dihglbcN.mm"
include "syl121anc.mm"
include "fveq2.mm"
include "iinxprg.mm"
include "3eqtrd.mm"

theorem dihmeetcN
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vq: setvar q
  let vx: setvar x
  assume dihmeetc.b: |- B = ( Base ` K )
  assume dihmeetc.l: |- .<_ = ( le ` K )
  assume dihmeetc.m: |- ./\ = ( meet ` K )
  assume dihmeetc.h: |- H = ( LHyp ` K )
  assume dihmeetc.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ Y e. B ) /\ -. ( X ./\ Y ) .<_ W ) -> ( I ` ( X ./\ Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cX
    cY
    c.an
    co
    #
    cW
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    @6
    cI
    cfv
    cX
    cY
    cpr
    #
    cK
    cglb
    cfv
    #
    cfv
    #
    cI
    cfv
    #
    vx
    @10
    vx
    cv
    #
    cI
    cfv
    #
    ciin
    #
    cX
    cI
    cfv
    #
    cY
    cI
    cfv
    #
    cin
    #
    @9
    @6
    @12
    cI
    @9
    @11
    cK
    c.an
    chlt
    cB
    cX
    cY
    cB
    @11
    eqid
    #
    dihmeetc.m
    @0
    @1
    @5
    @8
    simp1l
    @2
    @3
    @4
    @8
    simp2l
    #
    @2
    @3
    @4
    @8
    simp2r
    meetval
    #
    fveq2d
    @9
    @2
    @10
    cB
    wss
    #
    @10
    c0
    wne
    #
    @12
    cW
    c.le
    wbr
    #
    wn
    @13
    @16
    wceq
    @2
    @5
    @8
    simp1
    @5
    @2
    @23
    @8
    cX
    cY
    cB
    prssi
    3ad2ant2
    @9
    @3
    @24
    @21
    cX
    cY
    cB
    prnzg
    syl
    @9
    @7
    @25
    @2
    @5
    @8
    simp3
    @9
    @6
    @12
    cW
    c.le
    @22
    breq1d
    mtbid
    vx
    cB
    @10
    @11
    cH
    cI
    cK
    c.le
    cW
    dihmeetc.b
    @20
    dihmeetc.h
    dihmeetc.i
    dihmeetc.l
    dihglbcN
    syl121anc
    @5
    @2
    @16
    @19
    wceq
    @8
    vx
    cX
    cY
    @15
    @17
    @18
    cB
    cB
    @14
    cX
    cI
    fveq2
    @14
    cY
    cI
    fveq2
    iinxprg
    3ad2ant2
    3eqtrd
end
