include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "ccom.mm"
include "co.mm"
include "wceq.mm"
include "cid.mm"
include "cbs.mm"
include "cres.mm"
include "coeq1.mm"
include "wf1o.mm"
include "wf.mm"
include "eqid.mm"
include "ltrn1o.mm"
include "3adant2.mm"
include "f1of.mm"
include "fcoi2.mm"
include "3syl.mm"
include "sylan9eqr.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "cp0.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "trlcl.mm"
include "3adant3.mm"
include "latjidm.mm"
include "syl2anc.mm"
include "col.mm"
include "hlol.mm"
include "olj01.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "coeq2.mm"
include "fcoi1.mm"
include "wb.mm"
include "trlid0b.mm"
include "biimpa.mm"
include "3eqtr4d.mm"
include "cple.mm"
include "simp1.mm"
include "ltrnco.mm"
include "latjcl.mm"
include "syl3anc.mm"
include "wbr.mm"
include "latlej1.mm"
include "trlco.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simpr.mm"
include "eqbrtrd.mm"
include "eqbrtrrd.mm"
include "latasymd.mm"
include "wne.mm"
include "catm.mm"
include "simpl1l.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr1.mm"
include "trlnidat.mm"
include "simpl3.mm"
include "jca.mm"
include "simpr3.mm"
include "trlcoat.mm"
include "simpr2.mm"
include "trlcone.mm"
include "syl112anc.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "mpbid.mm"
include "pm2.61da3ne.mm"

theorem trljco
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let cW: class W
  assume trljco.j: |- .\/ = ( join ` K )
  assume trljco.h: |- H = ( LHyp ` K )
  assume trljco.t: |- T = ( ( LTrn ` K ) ` W )
  assume trljco.r: |- R = ( ( trL ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) -> ( ( R ` F ) .\/ ( R ` ( F o. G ) ) ) = ( ( R ` F ) .\/ ( R ` G ) ) )

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
    w3a
    #
    cF
    cR
    cfv
    #
    cF
    cG
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    @6
    cG
    cR
    cfv
    #
    c.or
    co
    #
    wceq
    #
    cF
    cid
    cK
    cbs
    cfv
    #
    cres
    #
    cG
    @14
    @6
    @10
    @5
    cF
    @14
    wceq
    #
    wa
    #
    @8
    @10
    @6
    c.or
    @16
    @7
    cG
    cR
    @15
    @5
    @7
    @14
    cG
    ccom
    #
    cG
    cF
    @14
    cG
    coeq1
    @5
    @13
    @13
    cG
    wf1o
    #
    @13
    @13
    cG
    wf
    @17
    cG
    wceq
    @2
    @4
    @18
    @3
    @13
    cT
    cG
    cH
    cK
    chlt
    cW
    @13
    eqid
    #
    trljco.h
    trljco.t
    ltrn1o
    3adant2
    @13
    @13
    cG
    f1of
    @13
    @13
    cG
    fcoi2
    3syl
    sylan9eqr
    fveq2d
    oveq2d
    @5
    cG
    @14
    wceq
    #
    wa
    #
    @6
    @6
    c.or
    co
    #
    @6
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    @9
    @11
    @5
    @22
    @24
    wceq
    @20
    @5
    @22
    @6
    @24
    @5
    cK
    clat
    wcel
    #
    @6
    @13
    wcel
    #
    @22
    @6
    wceq
    @5
    @0
    @25
    @0
    @1
    @3
    @4
    simp1l
    #
    cK
    hllat
    syl
    #
    @2
    @3
    @26
    @4
    @13
    cR
    cT
    cF
    cH
    cK
    cW
    @19
    trljco.h
    trljco.t
    trljco.r
    trlcl
    3adant3
    #
    @13
    c.or
    cK
    @6
    @19
    trljco.j
    latjidm
    syl2anc
    #
    @5
    cK
    col
    wcel
    #
    @26
    @24
    @6
    wceq
    @5
    @0
    @31
    @27
    cK
    hlol
    syl
    @29
    @13
    c.or
    cK
    @6
    @23
    @19
    trljco.j
    @23
    eqid
    #
    olj01
    syl2anc
    eqtr4d
    adantr
    @21
    @8
    @6
    @6
    c.or
    @21
    @7
    cF
    cR
    @20
    @5
    @7
    cF
    @14
    ccom
    #
    cF
    cG
    @14
    cF
    coeq2
    @5
    @13
    @13
    cF
    wf1o
    #
    @13
    @13
    cF
    wf
    @33
    cF
    wceq
    @2
    @3
    @34
    @4
    @13
    cT
    cF
    cH
    cK
    chlt
    cW
    @19
    trljco.h
    trljco.t
    ltrn1o
    3adant3
    @13
    @13
    cF
    f1of
    @13
    @13
    cF
    fcoi1
    3syl
    sylan9eqr
    fveq2d
    oveq2d
    @21
    @10
    @23
    @6
    c.or
    @5
    @20
    @10
    @23
    wceq
    #
    @2
    @4
    @20
    @35
    wb
    @3
    @13
    cR
    cT
    cG
    cH
    cK
    cW
    @23
    @19
    @32
    trljco.h
    trljco.t
    trljco.r
    trlid0b
    3adant2
    biimpa
    oveq2d
    3eqtr4d
    @5
    @6
    @10
    wceq
    #
    wa
    #
    @13
    cK
    cK
    cple
    cfv
    #
    @9
    @11
    @19
    @38
    eqid
    #
    @5
    @25
    @36
    @28
    adantr
    @5
    @9
    @13
    wcel
    #
    @36
    @5
    @25
    @26
    @8
    @13
    wcel
    #
    @40
    @28
    @29
    @5
    @2
    @7
    cT
    wcel
    @41
    @2
    @3
    @4
    simp1
    cT
    cF
    cG
    cH
    cK
    cW
    trljco.h
    trljco.t
    ltrnco
    @13
    cR
    cT
    @7
    cH
    cK
    cW
    @19
    trljco.h
    trljco.t
    trljco.r
    trlcl
    syl2anc
    #
    @13
    c.or
    cK
    @6
    @8
    @19
    trljco.j
    latjcl
    syl3anc
    adantr
    @5
    @11
    @13
    wcel
    #
    @36
    @5
    @25
    @26
    @10
    @13
    wcel
    #
    @43
    @28
    @29
    @2
    @4
    @44
    @3
    @13
    cR
    cT
    cG
    cH
    cK
    cW
    @19
    trljco.h
    trljco.t
    trljco.r
    trlcl
    3adant2
    #
    @13
    c.or
    cK
    @6
    @10
    @19
    trljco.j
    latjcl
    syl3anc
    #
    adantr
    @5
    @9
    @11
    @38
    wbr
    #
    @36
    @5
    @6
    @11
    @38
    wbr
    #
    @8
    @11
    @38
    wbr
    #
    @47
    @5
    @25
    @26
    @44
    @48
    @28
    @29
    @45
    @13
    c.or
    cK
    @38
    @6
    @10
    @19
    @39
    trljco.j
    latlej1
    syl3anc
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    @38
    cW
    @39
    trljco.j
    trljco.h
    trljco.t
    trljco.r
    trlco
    @5
    @25
    @26
    @41
    @43
    @48
    @49
    wa
    @47
    wb
    @28
    @29
    @42
    @46
    @13
    c.or
    cK
    @38
    @6
    @8
    @11
    @19
    @39
    trljco.j
    latjle12
    syl13anc
    mpbi2and
    #
    adantr
    @37
    @22
    @11
    @9
    @38
    @37
    @6
    @10
    @6
    c.or
    @5
    @36
    simpr
    oveq2d
    @5
    @22
    @9
    @38
    wbr
    @36
    @5
    @22
    @6
    @9
    @38
    @30
    @5
    @25
    @26
    @41
    @6
    @9
    @38
    wbr
    @28
    @29
    @42
    @13
    c.or
    cK
    @38
    @6
    @8
    @19
    @39
    trljco.j
    latlej1
    syl3anc
    eqbrtrd
    adantr
    eqbrtrrd
    latasymd
    @5
    cF
    @14
    wne
    #
    cG
    @14
    wne
    #
    @6
    @10
    wne
    #
    w3a
    #
    wa
    #
    @47
    @12
    @5
    @47
    @54
    @50
    adantr
    @55
    @0
    @6
    cK
    catm
    cfv
    #
    wcel
    #
    @8
    @56
    wcel
    #
    @6
    @8
    wne
    #
    @57
    @10
    @56
    wcel
    #
    @47
    @12
    wb
    @0
    @1
    @3
    @4
    @54
    simpl1l
    @55
    @2
    @3
    @51
    @57
    @2
    @3
    @4
    @54
    simpl1
    #
    @2
    @3
    @4
    @54
    simpl2
    #
    @5
    @51
    @52
    @53
    simpr1
    @56
    @13
    cR
    cT
    cF
    cH
    cK
    cW
    @19
    @56
    eqid
    #
    trljco.h
    trljco.t
    trljco.r
    trlnidat
    syl3anc
    #
    @55
    @2
    @3
    @4
    wa
    #
    @53
    @58
    @61
    @55
    @3
    @4
    @62
    @2
    @3
    @4
    @54
    simpl3
    #
    jca
    #
    @5
    @51
    @52
    @53
    simpr3
    #
    @56
    cR
    cT
    cF
    cG
    cH
    cK
    cW
    @63
    trljco.h
    trljco.t
    trljco.r
    trlcoat
    syl3anc
    @55
    @2
    @65
    @53
    @52
    @59
    @61
    @67
    @68
    @5
    @51
    @52
    @53
    simpr2
    #
    @13
    cR
    cT
    cF
    cG
    cH
    cK
    cW
    @19
    trljco.h
    trljco.t
    trljco.r
    trlcone
    syl112anc
    @64
    @55
    @2
    @4
    @52
    @60
    @61
    @66
    @69
    @56
    @13
    cR
    cT
    cG
    cH
    cK
    cW
    @19
    @63
    trljco.h
    trljco.t
    trljco.r
    trlnidat
    syl3anc
    @56
    @6
    @8
    @6
    @10
    c.or
    cK
    @38
    @39
    trljco.j
    @63
    ps-1
    syl132anc
    mpbid
    pm2.61da3ne
end
