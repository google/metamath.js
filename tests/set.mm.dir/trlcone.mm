include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wne.mm"
include "cid.mm"
include "cres.mm"
include "w3a.mm"
include "catm.mm"
include "ccom.mm"
include "cp0.mm"
include "wceq.mm"
include "simpl3l.mm"
include "cple.mm"
include "wbr.mm"
include "ccnv.mm"
include "cjn.mm"
include "co.mm"
include "simp11.mm"
include "simp12l.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "simp12r.mm"
include "ltrnco.mm"
include "syl3anc.mm"
include "eqid.mm"
include "trlco.mm"
include "coass.mm"
include "wf1o.mm"
include "ltrn1o.mm"
include "f1ococnv1.mm"
include "syl.mm"
include "coeq1d.mm"
include "wf.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "eqtrd.mm"
include "syl5reqr.mm"
include "fveq2d.mm"
include "simp11l.mm"
include "simp2.mm"
include "hlatjidm.mm"
include "trlcnv.mm"
include "eqcomd.mm"
include "simp3.mm"
include "oveq12d.mm"
include "eqtr3d.mm"
include "3brtr4d.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "simp13r.mm"
include "trlnidat.mm"
include "atcmp.mm"
include "mpbid.mm"
include "3expia.mm"
include "necon3d.mm"
include "mpd.mm"
include "simpl3r.mm"
include "simpl1.mm"
include "simpl2r.mm"
include "trlid0b.mm"
include "necon3bid.mm"
include "necomd.mm"
include "simpr.mm"
include "simpl2l.mm"
include "mpbird.mm"
include "3netr4d.mm"
include "wo.mm"
include "simp1.mm"
include "simp2l.mm"
include "trlator0.mm"
include "mpjaodan.mm"

theorem trlcone
  let cB: class B
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  assume trlcone.b: |- B = ( Base ` K )
  assume trlcone.h: |- H = ( LHyp ` K )
  assume trlcone.t: |- T = ( ( LTrn ` K ) ` W )
  assume trlcone.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( F e. T /\ G e. T ) /\ ( ( R ` F ) =/= ( R ` G ) /\ G =/= ( _I |` B ) ) ) -> ( R ` F ) =/= ( R ` ( F o. G ) ) )

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
    cG
    cT
    wcel
    #
    wa
    #
    cF
    cR
    cfv
    #
    cG
    cR
    cfv
    #
    wne
    #
    cG
    cid
    cB
    cres
    #
    wne
    #
    wa
    #
    w3a
    #
    @6
    cK
    catm
    cfv
    #
    wcel
    #
    @6
    cF
    cG
    ccom
    #
    cR
    cfv
    #
    wne
    #
    @6
    cK
    cp0
    cfv
    #
    wceq
    #
    @12
    @14
    wa
    #
    @8
    @17
    @8
    @10
    @2
    @5
    @14
    simpl3l
    @20
    @6
    @16
    @6
    @7
    @12
    @14
    @6
    @16
    wceq
    #
    @6
    @7
    wceq
    @12
    @14
    @21
    w3a
    #
    @7
    @6
    @22
    @7
    @6
    cK
    cple
    cfv
    #
    wbr
    #
    @7
    @6
    wceq
    #
    @22
    cF
    ccnv
    #
    @15
    ccom
    #
    cR
    cfv
    #
    @26
    cR
    cfv
    #
    @16
    cK
    cjn
    cfv
    #
    co
    #
    @7
    @6
    @23
    @22
    @2
    @26
    cT
    wcel
    #
    @15
    cT
    wcel
    #
    @28
    @31
    @23
    wbr
    @2
    @5
    @11
    @14
    @21
    simp11
    #
    @22
    @2
    @3
    @32
    @34
    @3
    @4
    @2
    @11
    @14
    @21
    simp12l
    #
    cT
    cF
    cH
    cK
    cW
    trlcone.h
    trlcone.t
    ltrncnv
    syl2anc
    @22
    @2
    @3
    @4
    @33
    @34
    @35
    @3
    @4
    @2
    @11
    @14
    @21
    simp12r
    #
    cT
    cF
    cG
    cH
    cK
    cW
    trlcone.h
    trlcone.t
    ltrnco
    syl3anc
    cR
    cT
    @26
    @15
    cH
    @30
    cK
    @23
    cW
    @23
    eqid
    #
    @30
    eqid
    #
    trlcone.h
    trlcone.t
    trlcone.r
    trlco
    syl3anc
    @22
    cG
    @27
    cR
    @22
    @27
    @26
    cF
    ccom
    #
    cG
    ccom
    #
    cG
    @26
    cF
    cG
    coass
    @22
    @40
    @9
    cG
    ccom
    #
    cG
    @22
    @39
    @9
    cG
    @22
    cB
    cB
    cF
    wf1o
    #
    @39
    @9
    wceq
    @22
    @2
    @3
    @42
    @34
    @35
    cB
    cT
    cF
    cH
    cK
    chlt
    cW
    trlcone.b
    trlcone.h
    trlcone.t
    ltrn1o
    syl2anc
    cB
    cB
    cF
    f1ococnv1
    syl
    coeq1d
    @22
    cB
    cB
    cG
    wf1o
    #
    cB
    cB
    cG
    wf
    #
    @41
    cG
    wceq
    #
    @22
    @2
    @4
    @43
    @34
    @36
    cB
    cT
    cG
    cH
    cK
    chlt
    cW
    trlcone.b
    trlcone.h
    trlcone.t
    ltrn1o
    #
    syl2anc
    cB
    cB
    cG
    f1of
    #
    cB
    cB
    cG
    fcoi2
    #
    3syl
    eqtrd
    syl5reqr
    fveq2d
    @22
    @6
    @6
    @30
    co
    #
    @6
    @31
    @22
    @0
    @14
    @49
    @6
    wceq
    @0
    @1
    @5
    @11
    @14
    @21
    simp11l
    #
    @12
    @14
    @21
    simp2
    #
    @13
    @30
    cK
    @6
    @38
    @13
    eqid
    #
    hlatjidm
    syl2anc
    @22
    @6
    @29
    @6
    @16
    @30
    @22
    @29
    @6
    @22
    @2
    @3
    @29
    @6
    wceq
    @34
    @35
    cR
    cT
    cF
    cH
    cK
    cW
    trlcone.h
    trlcone.t
    trlcone.r
    trlcnv
    syl2anc
    eqcomd
    @12
    @14
    @21
    simp3
    oveq12d
    eqtr3d
    3brtr4d
    @22
    cK
    cal
    wcel
    #
    @7
    @13
    wcel
    #
    @14
    @24
    @25
    wb
    @22
    @0
    @53
    @50
    cK
    hlatl
    syl
    @22
    @2
    @4
    @10
    @54
    @34
    @36
    @8
    @10
    @2
    @5
    @14
    @21
    simp13r
    @13
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    trlcone.b
    @52
    trlcone.h
    trlcone.t
    trlcone.r
    trlnidat
    syl3anc
    @51
    @13
    @7
    @6
    cK
    @23
    @37
    @52
    atcmp
    syl3anc
    mpbid
    eqcomd
    3expia
    necon3d
    mpd
    @12
    @19
    wa
    #
    @18
    @7
    @6
    @16
    @55
    @7
    @18
    @55
    @10
    @7
    @18
    wne
    @8
    @10
    @2
    @5
    @19
    simpl3r
    @55
    cG
    @9
    @7
    @18
    @55
    @2
    @4
    cG
    @9
    wceq
    @7
    @18
    wceq
    wb
    @2
    @5
    @11
    @19
    simpl1
    #
    @3
    @4
    @2
    @11
    @19
    simpl2r
    #
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    @18
    trlcone.b
    @18
    eqid
    #
    trlcone.h
    trlcone.t
    trlcone.r
    trlid0b
    syl2anc
    necon3bid
    mpbid
    necomd
    @12
    @19
    simpr
    #
    @55
    @15
    cG
    cR
    @55
    @15
    @41
    cG
    @55
    cF
    @9
    cG
    @55
    cF
    @9
    wceq
    #
    @19
    @59
    @55
    @2
    @3
    @60
    @19
    wb
    @56
    @3
    @4
    @2
    @11
    @19
    simpl2l
    cB
    cR
    cT
    cF
    cH
    cK
    cW
    @18
    trlcone.b
    @58
    trlcone.h
    trlcone.t
    trlcone.r
    trlid0b
    syl2anc
    mpbird
    coeq1d
    @55
    @43
    @44
    @45
    @55
    @2
    @4
    @43
    @56
    @57
    @46
    syl2anc
    @47
    @48
    3syl
    eqtrd
    fveq2d
    3netr4d
    @12
    @2
    @3
    @14
    @19
    wo
    @2
    @5
    @11
    simp1
    @2
    @3
    @4
    @11
    simp2l
    @13
    cR
    cT
    cF
    cH
    cK
    cW
    @18
    @58
    @52
    trlcone.h
    trlcone.t
    trlcone.r
    trlator0
    syl2anc
    mpjaodan
end
