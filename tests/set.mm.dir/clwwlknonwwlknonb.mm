include "cword.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cwwlksn.mm"
include "cc0.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cclwwlkn.mm"
include "cwwlksnon.mm"
include "cclwwlknon.mm"
include "s1eq.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "biimpac.mm"
include "adantl.mm"
include "chash.mm"
include "wi.mm"
include "cvv.mm"
include "fvexd.mm"
include "eleq1.mm"
include "mpbid.mm"
include "c1.mm"
include "caddc.mm"
include "cv.mm"
include "cpr.mm"
include "cedg.mm"
include "cfzo.mm"
include "wral.mm"
include "eqid.mm"
include "wwlknp.mm"
include "simprrl.mm"
include "wb.mm"
include "simpl.mm"
include "anim2i.mm"
include "ancomd.mm"
include "ccats1alpha.mm"
include "syl.mm"
include "simpr.mm"
include "syl6bi.mm"
include "com12.mm"
include "adantr.mm"
include "imp.mm"
include "cn0.mm"
include "nnnn0.mm"
include "ccatws1lenp1b.mm"
include "sylan2.mm"
include "biimpd.mm"
include "eqcomd.mm"
include "3jca.mm"
include "ex.mm"
include "3adant3.mm"
include "expd.mm"
include "sylbid.mm"
include "com13.mm"
include "imp32.mm"
include "ccats1val2.mm"
include "ccat1st1st.mm"
include "ad2antrr.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "ad2antll.mm"
include "eqtrd.mm"
include "jca31.mm"
include "idd.mm"
include "lbfzo0.mm"
include "biimpri.mm"
include "3anim123d.mm"
include "mpd.mm"
include "ccats1val1.mm"
include "expcom.mm"
include "com14.mm"
include "impcom.mm"
include "eqcoms.mm"
include "jca.mm"
include "syldc.mm"
include "impbid.mm"
include "clwwlknwwlksnb.mm"
include "anbi1d.mm"
include "3anan32.mm"
include "a1i.mm"
include "3bitr4rd.mm"
include "wwlknon.mm"
include "isclwwlknon.mm"

theorem clwwlknonwwlknonb
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let vi: setvar i
  assume clwwlknonwwlknonb.v: |- V = ( Vtx ` G )


  assert |- ( ( W e. Word V /\ N e. NN ) -> ( W e. ( X ( ClWWalksNOn ` G ) N ) <-> ( W ++ <" X "> ) e. ( X ( N WWalksNOn G ) X ) ) )

  proof
    cW
    cV
    cword
    #
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cW
    cX
    cs1
    #
    cconcat
    co
    #
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    cc0
    @5
    cfv
    #
    cX
    wceq
    #
    cN
    @5
    cfv
    cX
    wceq
    #
    w3a
    #
    cW
    cN
    cG
    cclwwlkn
    co
    wcel
    #
    cc0
    cW
    cfv
    #
    cX
    wceq
    #
    wa
    #
    @5
    cX
    cX
    cN
    cG
    cwwlksnon
    co
    co
    wcel
    #
    cW
    cX
    cN
    cG
    cclwwlknon
    cfv
    co
    wcel
    #
    @3
    cW
    @13
    cs1
    #
    cconcat
    co
    #
    @6
    wcel
    #
    @14
    wa
    #
    @7
    @10
    wa
    #
    @9
    wa
    #
    @15
    @11
    @3
    @21
    @23
    @3
    @21
    @23
    @3
    @21
    wa
    #
    @7
    @10
    @9
    @21
    @7
    @3
    @14
    @20
    @7
    @14
    @19
    @5
    @6
    @14
    @18
    @4
    cW
    cconcat
    @13
    cX
    s1eq
    oveq2d
    #
    eleq1d
    #
    biimpac
    adantl
    @24
    @1
    cX
    cV
    wcel
    #
    cN
    cW
    chash
    cfv
    #
    wceq
    #
    w3a
    #
    @10
    @3
    @20
    @14
    @30
    @14
    @20
    @3
    @30
    @14
    @20
    @7
    @3
    @30
    wi
    #
    @26
    @14
    cX
    cvv
    wcel
    #
    @7
    @31
    wi
    @14
    @13
    cvv
    wcel
    @32
    @14
    cc0
    cW
    fvexd
    @13
    cX
    cvv
    eleq1
    mpbid
    @7
    @32
    @31
    @7
    @32
    @3
    @30
    @7
    @5
    @0
    wcel
    #
    @5
    chash
    cfv
    cN
    c1
    caddc
    co
    wceq
    #
    vi
    cv
    #
    @5
    cfv
    @35
    c1
    caddc
    co
    @5
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    cN
    cfzo
    co
    wral
    #
    w3a
    @32
    @3
    wa
    #
    @30
    wi
    #
    vi
    @36
    cG
    cN
    cV
    @5
    clwwlknonwwlknonb.v
    @36
    eqid
    wwlknp
    @33
    @34
    @39
    @37
    @33
    @34
    wa
    #
    @38
    @30
    @40
    @38
    wa
    #
    @1
    @27
    @29
    @40
    @32
    @1
    @2
    simprrl
    @40
    @38
    @27
    @33
    @38
    @27
    wi
    @34
    @38
    @33
    @27
    @38
    @33
    @1
    @27
    wa
    #
    @27
    @38
    @1
    @32
    wa
    @33
    @42
    wb
    @38
    @32
    @1
    @3
    @1
    @32
    @1
    @2
    simpl
    anim2i
    ancomd
    cW
    cV
    cvv
    cV
    cX
    ccats1alpha
    syl
    @1
    @27
    simpr
    syl6bi
    com12
    adantr
    imp
    @41
    @28
    cN
    @40
    @38
    @28
    cN
    wceq
    #
    @34
    @38
    @43
    wi
    @33
    @38
    @34
    @43
    @3
    @34
    @43
    wi
    @32
    @3
    @34
    @43
    @2
    @1
    cN
    cn0
    wcel
    @34
    @43
    wb
    cN
    nnnn0
    cN
    cV
    cW
    cX
    ccatws1lenp1b
    sylan2
    biimpd
    adantl
    com12
    adantl
    imp
    eqcomd
    3jca
    ex
    3adant3
    syl
    #
    expd
    com12
    syl
    sylbid
    com13
    imp32
    cX
    cN
    cV
    cW
    ccats1val2
    syl
    @24
    @8
    @13
    cX
    @24
    cc0
    @19
    cfv
    #
    @13
    wceq
    #
    @8
    @13
    wceq
    #
    @1
    @46
    @2
    @21
    cV
    cW
    ccat1st1st
    ad2antrr
    @14
    @46
    @47
    wb
    @3
    @20
    @14
    @45
    @8
    @13
    @14
    cc0
    @19
    @5
    @25
    fveq1d
    eqeq1d
    ad2antll
    mpbid
    @21
    @14
    @3
    @20
    @14
    simpr
    adantl
    eqtrd
    jca31
    ex
    @23
    @3
    @14
    @21
    @9
    @22
    @3
    @14
    wi
    #
    @9
    @32
    @22
    @48
    wi
    @9
    @8
    cvv
    wcel
    @32
    @9
    cc0
    @5
    fvexd
    @8
    cX
    cvv
    eleq1
    mpbid
    @3
    @32
    @22
    @9
    @14
    @32
    @3
    @22
    @9
    @14
    wi
    #
    wi
    @22
    @38
    @49
    @7
    @38
    @49
    wi
    @10
    @7
    @38
    @49
    @7
    @38
    wa
    #
    @9
    @14
    @50
    @8
    @13
    cX
    @50
    @1
    @27
    cc0
    cc0
    @28
    cfzo
    co
    wcel
    #
    w3a
    #
    @47
    @50
    @30
    @52
    @7
    @38
    @30
    @44
    imp
    @50
    @1
    @1
    @27
    @27
    @29
    @51
    @50
    @1
    idd
    @50
    @27
    idd
    @3
    @29
    @51
    wi
    #
    @7
    @32
    @2
    @53
    @1
    @29
    @2
    @51
    @29
    @2
    @28
    cn
    wcel
    #
    @51
    cN
    @28
    cn
    eleq1
    @51
    @54
    @28
    lbfzo0
    biimpri
    syl6bi
    com12
    adantl
    ad2antll
    3anim123d
    mpd
    cX
    cc0
    cV
    cW
    ccats1val1
    syl
    eqeq1d
    biimpd
    ex
    adantr
    com12
    expcom
    com14
    mpd
    impcom
    @7
    @14
    @21
    wi
    @10
    @9
    @7
    @14
    @21
    @7
    @14
    wa
    @20
    @14
    @14
    @7
    @20
    @14
    @5
    @19
    @6
    @14
    @4
    @18
    cW
    cconcat
    @4
    @18
    wceq
    cX
    @13
    cX
    @13
    s1eq
    eqcoms
    oveq2d
    eleq1d
    biimpac
    @7
    @14
    simpr
    jca
    ex
    ad2antrr
    syldc
    impbid
    @3
    @12
    @20
    @14
    cG
    cN
    cV
    cW
    clwwlknonwwlknonb.v
    clwwlknwwlksnb
    anbi1d
    @11
    @23
    wb
    @3
    @7
    @9
    @10
    3anan32
    a1i
    3bitr4rd
    @16
    @11
    wb
    @3
    cX
    cX
    cG
    cN
    @5
    wwlknon
    a1i
    @17
    @15
    wb
    @3
    cG
    cN
    cW
    cX
    isclwwlknon
    a1i
    3bitr4rd
end
