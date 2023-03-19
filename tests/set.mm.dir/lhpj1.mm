include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "catm.mm"
include "cfv.mm"
include "wrex.mm"
include "wb.mm"
include "simpll.mm"
include "simpr.mm"
include "lhpbase.mm"
include "ad2antlr.mm"
include "eqid.mm"
include "hlrelat2.mm"
include "syl3anc.mm"
include "w3a.mm"
include "simp1l.mm"
include "simp2.mm"
include "simp3r.mm"
include "lhpjat1.mm"
include "syl12anc.mm"
include "simp3l.mm"
include "clat.mm"
include "wi.mm"
include "simp1ll.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "3ad2ant2.mm"
include "simp1r.mm"
include "3ad2ant1.mm"
include "latjlej2.mm"
include "syl13anc.mm"
include "mpd.mm"
include "eqbrtrrd.mm"
include "cops.mm"
include "hlop.mm"
include "latjcl.mm"
include "op1le.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "rexlimdv3a.mm"
include "sylbid.mm"
include "impr.mm"

theorem lhpj1
  let cB: class B
  let c.1: class .1.
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let cX: class X
  let vp: setvar p
  assume lhpj1.b: |- B = ( Base ` K )
  assume lhpj1.l: |- .<_ = ( le ` K )
  assume lhpj1.j: |- .\/ = ( join ` K )
  assume lhpj1.u: |- .1. = ( 1. ` K )
  assume lhpj1.h: |- H = ( LHyp ` K )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( X e. B /\ -. X .<_ W ) ) -> ( W .\/ X ) = .1. )

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
    cX
    cW
    c.le
    wbr
    wn
    #
    cW
    cX
    c.or
    co
    #
    c.1
    wceq
    #
    @2
    @3
    wa
    #
    @4
    vp
    cv
    #
    cX
    c.le
    wbr
    #
    @8
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    vp
    cK
    catm
    cfv
    #
    wrex
    #
    @6
    @7
    @0
    @3
    cW
    cB
    wcel
    #
    @4
    @13
    wb
    @0
    @1
    @3
    simpll
    @2
    @3
    simpr
    @1
    @14
    @0
    @3
    cB
    cH
    cK
    cW
    lhpj1.b
    lhpj1.h
    lhpbase
    ad2antlr
    #
    @12
    cB
    cK
    c.le
    cX
    cW
    vp
    lhpj1.b
    lhpj1.l
    @12
    eqid
    #
    hlrelat2
    syl3anc
    @7
    @11
    @6
    vp
    @12
    @7
    @8
    @12
    wcel
    #
    @11
    w3a
    #
    c.1
    @5
    c.le
    wbr
    #
    @6
    @18
    cW
    @8
    c.or
    co
    #
    c.1
    @5
    c.le
    @18
    @2
    @17
    @10
    @20
    c.1
    wceq
    @2
    @3
    @17
    @11
    simp1l
    @7
    @17
    @11
    simp2
    @7
    @17
    @9
    @10
    simp3r
    @12
    @8
    c.1
    cH
    c.or
    cK
    c.le
    cW
    lhpj1.l
    lhpj1.j
    lhpj1.u
    @16
    lhpj1.h
    lhpjat1
    syl12anc
    @18
    @9
    @20
    @5
    c.le
    wbr
    #
    @7
    @17
    @9
    @10
    simp3l
    @18
    cK
    clat
    wcel
    #
    @8
    cB
    wcel
    #
    @3
    @14
    @9
    @21
    wi
    @18
    @0
    @22
    @0
    @1
    @3
    @17
    @11
    simp1ll
    #
    cK
    hllat
    syl
    #
    @17
    @7
    @23
    @11
    @12
    cB
    @8
    cK
    lhpj1.b
    @16
    atbase
    3ad2ant2
    @2
    @3
    @17
    @11
    simp1r
    #
    @7
    @17
    @14
    @11
    @15
    3ad2ant1
    #
    cB
    c.or
    cK
    c.le
    @8
    cX
    cW
    lhpj1.b
    lhpj1.l
    lhpj1.j
    latjlej2
    syl13anc
    mpd
    eqbrtrrd
    @18
    cK
    cops
    wcel
    #
    @5
    cB
    wcel
    #
    @19
    @6
    wb
    @18
    @0
    @28
    @24
    cK
    hlop
    syl
    @18
    @22
    @14
    @3
    @29
    @25
    @27
    @26
    cB
    c.or
    cK
    cW
    cX
    lhpj1.b
    lhpj1.j
    latjcl
    syl3anc
    cB
    c.1
    cK
    c.le
    @5
    lhpj1.b
    lhpj1.l
    lhpj1.u
    op1le
    syl2anc
    mpbid
    rexlimdv3a
    sylbid
    impr
end
