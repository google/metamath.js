include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cfv.mm"
include "w3a.mm"
include "ccom.mm"
include "catm.mm"
include "cjn.mm"
include "co.mm"
include "cple.mm"
include "wbr.mm"
include "simpl1l.mm"
include "simp1.mm"
include "simp2r.mm"
include "simp32.mm"
include "eqid.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "adantr.mm"
include "simp2l.mm"
include "simp31.mm"
include "simpl33.mm"
include "simpr.mm"
include "ccnv.mm"
include "ltrnco.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "trlco.mm"
include "coass.mm"
include "wf1o.mm"
include "wceq.mm"
include "ltrn1o.mm"
include "f1ococnv2.mm"
include "syl.mm"
include "coeq2d.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi1.mm"
include "3syl.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "trlcnv.mm"
include "oveq2d.mm"
include "3brtr3d.mm"
include "hlatlej2.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "2atjlej.mm"
include "syl133anc.mm"
include "wn.mm"
include "nelne2.mm"
include "necomd.mm"
include "sylan.mm"
include "pm2.61dan.mm"

theorem cdlemg46
  let cB: class B
  let cR: class R
  let cT: class T
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cK: class K
  let cW: class W
  assume cdlemg46.b: |- B = ( Base ` K )
  assume cdlemg46.h: |- H = ( LHyp ` K )
  assume cdlemg46.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg46.r: |- R = ( ( trL ` K ) ` W )

  disjoint F h
  disjoint H h
  disjoint K h
  disjoint R h
  disjoint T h
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ h e. T ) /\ ( F =/= ( _I |` B ) /\ h =/= ( _I |` B ) /\ ( R ` h ) =/= ( R ` F ) ) ) -> ( R ` ( h o. F ) ) =/= ( R ` F ) )

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
    cF
    cT
    wcel
    #
    vh
    cv
    #
    cT
    wcel
    #
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    @4
    @7
    wne
    #
    @4
    cR
    cfv
    #
    cF
    cR
    cfv
    #
    wne
    #
    w3a
    #
    w3a
    #
    @4
    cF
    ccom
    #
    cR
    cfv
    #
    cK
    catm
    cfv
    #
    wcel
    #
    @16
    @11
    wne
    #
    @14
    @18
    wa
    #
    @0
    @10
    @17
    wcel
    #
    @11
    @17
    wcel
    #
    @12
    @18
    @22
    @10
    @11
    cK
    cjn
    cfv
    #
    co
    @16
    @11
    @23
    co
    #
    cK
    cple
    cfv
    #
    wbr
    #
    @19
    @0
    @1
    @6
    @13
    @18
    simpl1l
    #
    @14
    @21
    @18
    @14
    @2
    @5
    @9
    @21
    @2
    @6
    @13
    simp1
    #
    @2
    @3
    @5
    @13
    simp2r
    #
    @2
    @6
    @8
    @9
    @12
    simp32
    @17
    cB
    cR
    cT
    @4
    cH
    cK
    cW
    cdlemg46.b
    @17
    eqid
    #
    cdlemg46.h
    cdlemg46.t
    cdlemg46.r
    trlnidat
    syl3anc
    adantr
    #
    @14
    @22
    @18
    @14
    @2
    @3
    @8
    @22
    @28
    @2
    @3
    @5
    @13
    simp2l
    #
    @2
    @6
    @8
    @9
    @12
    simp31
    @17
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemg46.b
    @30
    cdlemg46.h
    cdlemg46.t
    cdlemg46.r
    trlnidat
    syl3anc
    #
    adantr
    #
    @8
    @9
    @12
    @2
    @6
    @18
    simpl33
    @14
    @18
    simpr
    #
    @34
    @20
    @10
    @24
    @25
    wbr
    #
    @11
    @24
    @25
    wbr
    #
    @26
    @14
    @36
    @18
    @14
    @15
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    @16
    @38
    cR
    cfv
    #
    @23
    co
    #
    @10
    @24
    @25
    @14
    @2
    @15
    cT
    wcel
    #
    @38
    cT
    wcel
    #
    @40
    @42
    @25
    wbr
    @28
    @14
    @2
    @5
    @3
    @43
    @28
    @29
    @32
    cT
    @4
    cF
    cH
    cK
    cW
    cdlemg46.h
    cdlemg46.t
    ltrnco
    syl3anc
    @14
    @2
    @3
    @44
    @28
    @32
    cT
    cF
    cH
    cK
    cW
    cdlemg46.h
    cdlemg46.t
    ltrncnv
    syl2anc
    cR
    cT
    @15
    @38
    cH
    @23
    cK
    @25
    cW
    @25
    eqid
    #
    @23
    eqid
    #
    cdlemg46.h
    cdlemg46.t
    cdlemg46.r
    trlco
    syl3anc
    @14
    @39
    @4
    cR
    @14
    @39
    @4
    cF
    @38
    ccom
    #
    ccom
    #
    @4
    @4
    cF
    @38
    coass
    @14
    @48
    @4
    @7
    ccom
    #
    @4
    @14
    @47
    @7
    @4
    @14
    cB
    cB
    cF
    wf1o
    #
    @47
    @7
    wceq
    @14
    @2
    @3
    @50
    @28
    @32
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    cdlemg46.b
    cdlemg46.h
    cdlemg46.t
    ltrn1o
    syl2anc
    cB
    cB
    cF
    f1ococnv2
    syl
    coeq2d
    @14
    cB
    cB
    @4
    wf1o
    #
    cB
    cB
    @4
    wf
    @49
    @4
    wceq
    @14
    @2
    @5
    @51
    @28
    @29
    cB
    cT
    @4
    cH
    cK
    chlt
    cW
    cdlemg46.b
    cdlemg46.h
    cdlemg46.t
    ltrn1o
    syl2anc
    cB
    cB
    @4
    f1of
    cB
    cB
    @4
    fcoi1
    3syl
    eqtrd
    syl5eq
    fveq2d
    @14
    @41
    @11
    @16
    @23
    @14
    @2
    @3
    @41
    @11
    wceq
    @28
    @32
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemg46.h
    cdlemg46.t
    cdlemg46.r
    trlcnv
    syl2anc
    oveq2d
    3brtr3d
    adantr
    @20
    @0
    @18
    @22
    @37
    @27
    @35
    @34
    @17
    @16
    @11
    @23
    cK
    @25
    @45
    @46
    @30
    hlatlej2
    syl3anc
    @20
    cK
    clat
    wcel
    #
    @10
    cB
    wcel
    #
    @11
    cB
    wcel
    #
    @24
    cB
    wcel
    #
    @36
    @37
    wa
    @26
    wb
    @20
    @0
    @52
    @27
    cK
    hllat
    syl
    @20
    @21
    @53
    @31
    @17
    cB
    @10
    cK
    cdlemg46.b
    @30
    atbase
    syl
    @20
    @22
    @54
    @34
    @17
    cB
    @11
    cK
    cdlemg46.b
    @30
    atbase
    syl
    @20
    @0
    @18
    @22
    @55
    @27
    @35
    @34
    @17
    cB
    @23
    cK
    @16
    @11
    cdlemg46.b
    @46
    @30
    hlatjcl
    syl3anc
    cB
    @23
    cK
    @25
    @10
    @11
    @24
    cdlemg46.b
    @45
    @46
    latjle12
    syl13anc
    mpbi2and
    @17
    @10
    @11
    @16
    @11
    @23
    cK
    @25
    @45
    @46
    @30
    2atjlej
    syl133anc
    @14
    @22
    @18
    wn
    #
    @19
    @33
    @22
    @56
    wa
    @11
    @16
    @11
    @16
    @17
    nelne2
    necomd
    sylan
    pm2.61dan
end
