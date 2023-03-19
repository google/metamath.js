include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "wne.mm"
include "w3a.mm"
include "cp0.mm"
include "cfv.mm"
include "co.mm"
include "cal.mm"
include "simp11l.mm"
include "hlatl.mm"
include "syl.mm"
include "simp3l.mm"
include "eqid.mm"
include "atn0.mm"
include "syl2anc.mm"
include "cmee.mm"
include "wceq.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "atbase.mm"
include "simp12l.mm"
include "simp2l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "latleeqm2.mm"
include "lhp2at0.mm"
include "eqeq1.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "necon3ad.mm"
include "mpd.mm"

theorem lhp2atnle
  let cA: class A
  let cP: class P
  let cU: class U
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cW: class W
  assume lhp2atnle.l: |- .<_ = ( le ` K )
  assume lhp2atnle.j: |- .\/ = ( join ` K )
  assume lhp2atnle.a: |- A = ( Atoms ` K )
  assume lhp2atnle.h: |- H = ( LHyp ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ U =/= V ) /\ ( U e. A /\ U .<_ W ) /\ ( V e. A /\ V .<_ W ) ) -> -. V .<_ ( P .\/ U ) )

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
    cP
    cA
    wcel
    #
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cU
    cV
    wne
    #
    w3a
    #
    cU
    cA
    wcel
    #
    cU
    cW
    c.le
    wbr
    #
    wa
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cV
    cK
    cp0
    cfv
    #
    wne
    #
    cV
    cP
    cU
    c.or
    co
    #
    c.le
    wbr
    #
    wn
    @14
    cK
    cal
    wcel
    #
    @11
    @16
    @14
    @0
    @19
    @0
    @1
    @5
    @6
    @10
    @13
    simp11l
    #
    cK
    hlatl
    syl
    @7
    @10
    @11
    @12
    simp3l
    #
    cA
    cV
    cK
    @15
    @15
    eqid
    #
    lhp2atnle.a
    atn0
    syl2anc
    @14
    @18
    cV
    @15
    @14
    @18
    @17
    cV
    cK
    cmee
    cfv
    #
    co
    #
    cV
    wceq
    #
    cV
    @15
    wceq
    #
    @14
    cK
    clat
    wcel
    #
    cV
    cK
    cbs
    cfv
    #
    wcel
    #
    @17
    @28
    wcel
    #
    @18
    @25
    wb
    @14
    @0
    @27
    @20
    cK
    hllat
    syl
    @14
    @11
    @29
    @21
    cA
    @28
    cV
    cK
    @28
    eqid
    #
    lhp2atnle.a
    atbase
    syl
    @14
    @0
    @3
    @8
    @30
    @20
    @3
    @4
    @2
    @6
    @10
    @13
    simp12l
    @7
    @8
    @9
    @13
    simp2l
    cA
    @28
    c.or
    cK
    cP
    cU
    @31
    lhp2atnle.j
    lhp2atnle.a
    hlatjcl
    syl3anc
    @28
    cK
    c.le
    @23
    cV
    @17
    @31
    lhp2atnle.l
    @23
    eqid
    #
    latleeqm2
    syl3anc
    @14
    @24
    @15
    wceq
    @25
    @26
    cA
    cP
    cU
    cH
    c.or
    cK
    c.le
    @23
    cV
    cW
    @15
    lhp2atnle.l
    lhp2atnle.j
    @32
    @22
    lhp2atnle.a
    lhp2atnle.h
    lhp2at0
    @24
    cV
    @15
    eqeq1
    syl5ibcom
    sylbid
    necon3ad
    mpd
end
