include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cpr.mm"
include "cglb.mm"
include "cv.mm"
include "ciin.mm"
include "cin.mm"
include "eqid.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp3.mm"
include "meetval.mm"
include "fveq2d.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "simp1.mm"
include "prssi.mm"
include "3adant1.mm"
include "prnzg.mm"
include "3ad2ant2.mm"
include "dihglb.mm"
include "syl12anc.mm"
include "fveq2.mm"
include "iinxprg.mm"
include "3eqtrd.mm"

theorem dihmeet
  let cB: class B
  let cH: class H
  let cI: class I
  let cK: class K
  let c.an: class ./\
  let cW: class W
  let cX: class X
  let cY: class Y
  let vx: setvar x
  assume dihmeet.b: |- B = ( Base ` K )
  assume dihmeet.m: |- ./\ = ( meet ` K )
  assume dihmeet.h: |- H = ( LHyp ` K )
  assume dihmeet.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. B /\ Y e. B ) -> ( I ` ( X ./\ Y ) ) = ( ( I ` X ) i^i ( I ` Y ) ) )

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
    w3a
    #
    cX
    cY
    c.an
    co
    #
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
    @7
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
    @5
    @6
    @9
    cI
    @5
    @8
    cK
    c.an
    chlt
    cB
    cX
    cY
    cB
    @8
    eqid
    #
    dihmeet.m
    @0
    @1
    @3
    @4
    simp1l
    @2
    @3
    @4
    simp2
    @2
    @3
    @4
    simp3
    meetval
    fveq2d
    @5
    @2
    @7
    cB
    wss
    #
    @7
    c0
    wne
    #
    @10
    @13
    wceq
    @2
    @3
    @4
    simp1
    @3
    @4
    @18
    @2
    cX
    cY
    cB
    prssi
    3adant1
    @3
    @2
    @19
    @4
    cX
    cY
    cB
    prnzg
    3ad2ant2
    vx
    cB
    @7
    @8
    cH
    cI
    cK
    cW
    dihmeet.b
    @17
    dihmeet.h
    dihmeet.i
    dihglb
    syl12anc
    @3
    @4
    @13
    @16
    wceq
    @2
    vx
    cX
    cY
    @12
    @14
    @15
    cB
    cB
    @11
    cX
    cI
    fveq2
    @11
    cY
    cI
    fveq2
    iinxprg
    3adant1
    3eqtrd
end
