include "wcel.mm"
include "cv.mm"
include "wdisj.mm"
include "wa.mm"
include "cfn.mm"
include "cuni.mm"
include "chash.mm"
include "cfv.mm"
include "cesum.mm"
include "wceq.mm"
include "wss.mm"
include "w3a.mm"
include "csu.mm"
include "nfdisj1.mm"
include "nfv.mm"
include "nf3an.mm"
include "simp2.mm"
include "simp3.mm"
include "simp1.mm"
include "hashunif.mm"
include "simpl.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wral.mm"
include "dfss3.mm"
include "cn0.mm"
include "hashcl.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "syl.mm"
include "ralimi.mm"
include "sylbi.mm"
include "r19.21bi.mm"
include "adantll.mm"
include "esumpfinval.mm"
include "3adant1.mm"
include "eqtr4d.mm"
include "3adant1l.mm"
include "3expa.mm"
include "wn.mm"
include "cvv.mm"
include "uniexg.mm"
include "wrex.mm"
include "notbii.mm"
include "rexnal.mm"
include "bitr4i.mm"
include "wi.mm"
include "elssuni.mm"
include "ssfi.mm"
include "expcom.mm"
include "con3d.mm"
include "rexlimiv.mm"
include "hashinf.mm"
include "syl2an.mm"
include "vex.mm"
include "mpan.mm"
include "reximi.mm"
include "nfre1.mm"
include "nfan.mm"
include "cicc.mm"
include "wf.mm"
include "hashf2.mm"
include "ffvelrn.mm"
include "mp2an.mm"
include "a1i.mm"
include "simpr.mm"
include "esumpinfval.mm"
include "sylan2.mm"
include "3adant2.mm"
include "3adant1r.mm"
include "pm2.61dan.mm"
include "cpw.mm"
include "pwfi.mm"
include "pwuni.mm"
include "mpan2.mm"
include "con3i.mm"
include "crab.mm"
include "cxad.mm"
include "cun.mm"
include "wtru.mm"
include "nftru.mm"
include "wo.mm"
include "unrab.mm"
include "exmid.mm"
include "rgenw.mm"
include "rabid2.mm"
include "mpbir.mm"
include "eqtr4i.mm"
include "esumeq1d.mm"
include "trud.mm"
include "nfrab1.mm"
include "rabexg.mm"
include "cin.mm"
include "c0.mm"
include "rabnc.mm"
include "esumsplit.mm"
include "syl5eqr.mm"
include "adantr.mm"
include "c1.mm"
include "cdif.mm"
include "csn.mm"
include "cab.mm"
include "dfrab3.mm"
include "wb.mm"
include "hasheq0.mm"
include "ax-mp.mm"
include "abbii.mm"
include "df-sn.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "snfi.mm"
include "inss2.mm"
include "eqeltri.mm"
include "difinf.mm"
include "syl2anc.mm"
include "notrab.mm"
include "eleq1i.mm"
include "sylnib.mm"
include "wne.mm"
include "rabid.mm"
include "sylib.mm"
include "simprd.mm"
include "biimpri.mm"
include "necon3bi.mm"
include "hashge1.mm"
include "cxr.mm"
include "1re.mm"
include "rexri.mm"
include "clt.mm"
include "0lt1.mm"
include "esumpinfsum.mm"
include "oveq2d.mm"
include "cmnf.mm"
include "iccssxr.mm"
include "ralrimiva.mm"
include "esumcl.mm"
include "sseldi.mm"
include "xrge0neqmnf.mm"
include "xaddpnf1.mm"
include "3eqtrd.mm"
include "adantlr.mm"

theorem hasheuni
  let vx: setvar x
  let cA: class A
  let cV: class V

  disjoint A x
  disjoint V x
  assert |- ( ( A e. V /\ Disj_ x e. A x ) -> ( # ` U. A ) = sum* x e. A ( # ` x ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    vx
    cv
    #
    wdisj
    #
    wa
    #
    cA
    cfn
    wcel
    #
    cA
    cuni
    #
    chash
    cfv
    #
    cA
    @1
    chash
    cfv
    #
    vx
    cesum
    #
    wceq
    #
    @3
    @4
    wa
    cA
    cfn
    wss
    #
    @9
    @3
    @4
    @10
    @9
    @2
    @4
    @10
    @9
    @0
    @2
    @4
    @10
    w3a
    #
    @6
    cA
    @7
    vx
    csu
    #
    @8
    @11
    vx
    cA
    @2
    @4
    @10
    vx
    vx
    cA
    @1
    nfdisj1
    @4
    vx
    nfv
    @10
    vx
    nfv
    nf3an
    @2
    @4
    @10
    simp2
    @2
    @4
    @10
    simp3
    @2
    @4
    @10
    simp1
    hashunif
    @4
    @10
    @8
    @12
    wceq
    @2
    @4
    @10
    wa
    cA
    @7
    vx
    @4
    @10
    simpl
    @10
    @1
    cA
    wcel
    #
    @7
    cc0
    cpnf
    cico
    co
    wcel
    #
    @4
    @10
    @14
    vx
    cA
    @10
    @1
    cfn
    wcel
    #
    vx
    cA
    wral
    #
    @14
    vx
    cA
    wral
    vx
    cA
    cfn
    dfss3
    #
    @15
    @14
    vx
    cA
    @15
    @7
    cn0
    wcel
    #
    @14
    @1
    hashcl
    @18
    @7
    cr
    wcel
    cc0
    @7
    cle
    wbr
    @14
    @7
    nn0re
    @7
    nn0ge0
    @7
    elrege0
    sylanbrc
    syl
    ralimi
    sylbi
    r19.21bi
    adantll
    esumpfinval
    3adant1
    eqtr4d
    3adant1l
    3expa
    @3
    @4
    @10
    wn
    #
    @9
    @0
    @4
    @19
    @9
    @2
    @0
    @19
    @9
    @4
    @0
    @19
    wa
    @6
    cpnf
    @8
    @0
    @5
    cvv
    wcel
    #
    @5
    cfn
    wcel
    #
    wn
    #
    @6
    cpnf
    wceq
    #
    @19
    cA
    cV
    uniexg
    #
    @19
    @15
    wn
    #
    vx
    cA
    wrex
    #
    @22
    @19
    @16
    wn
    @26
    @10
    @16
    @17
    notbii
    @15
    vx
    cA
    rexnal
    bitr4i
    #
    @25
    @22
    vx
    cA
    @13
    @1
    @5
    wss
    #
    @25
    @22
    wi
    @1
    cA
    elssuni
    @28
    @21
    @15
    @21
    @28
    @15
    @5
    @1
    ssfi
    expcom
    con3d
    syl
    rexlimiv
    sylbi
    @5
    cvv
    hashinf
    #
    syl2an
    @19
    @0
    @7
    cpnf
    wceq
    #
    vx
    cA
    wrex
    #
    @8
    cpnf
    wceq
    @19
    @26
    @31
    @27
    @25
    @30
    vx
    cA
    @1
    cvv
    wcel
    #
    @25
    @30
    vx
    vex
    #
    @1
    cvv
    hashinf
    mpan
    reximi
    sylbi
    @0
    @31
    wa
    #
    cA
    @7
    vx
    cV
    @0
    @31
    vx
    @0
    vx
    nfv
    #
    @30
    vx
    cA
    nfre1
    nfan
    @0
    @31
    simpl
    @7
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @34
    @13
    wa
    cvv
    @36
    chash
    wf
    @32
    @37
    hashf2
    @33
    cvv
    @36
    @1
    chash
    ffvelrn
    mp2an
    #
    a1i
    @0
    @31
    simpr
    esumpinfval
    sylan2
    eqtr4d
    3adant2
    3adant1r
    3expa
    pm2.61dan
    @0
    @4
    wn
    #
    @9
    @2
    @0
    @39
    wa
    #
    @6
    cpnf
    @8
    @0
    @20
    @22
    @23
    @39
    @24
    @21
    @4
    @21
    @5
    cpw
    #
    cfn
    wcel
    #
    @4
    @5
    pwfi
    @42
    cA
    @41
    wss
    @4
    cA
    pwuni
    @41
    cA
    ssfi
    mpan2
    sylbi
    con3i
    @29
    syl2an
    @40
    @8
    @7
    cc0
    wceq
    #
    vx
    cA
    crab
    #
    @7
    vx
    cesum
    #
    @43
    wn
    #
    vx
    cA
    crab
    #
    @7
    vx
    cesum
    #
    cxad
    co
    #
    @45
    cpnf
    cxad
    co
    #
    cpnf
    @0
    @8
    @49
    wceq
    @39
    @0
    @8
    @44
    @47
    cun
    #
    @7
    vx
    cesum
    #
    @49
    @52
    @8
    wceq
    wtru
    @51
    cA
    @7
    vx
    vx
    nftru
    @51
    cA
    wceq
    wtru
    @51
    @43
    @46
    wo
    #
    vx
    cA
    crab
    #
    cA
    @43
    @46
    vx
    cA
    unrab
    cA
    @54
    wceq
    @53
    vx
    cA
    wral
    @53
    vx
    cA
    @43
    exmid
    rgenw
    @53
    vx
    cA
    rabid2
    mpbir
    eqtr4i
    a1i
    esumeq1d
    trud
    @0
    @44
    @47
    @7
    vx
    @35
    @43
    vx
    cA
    nfrab1
    #
    @46
    vx
    cA
    nfrab1
    #
    @43
    vx
    cA
    cV
    rabexg
    #
    @46
    vx
    cA
    cV
    rabexg
    #
    @44
    @47
    cin
    c0
    wceq
    @0
    @43
    vx
    cA
    rabnc
    a1i
    @37
    @0
    @1
    @44
    wcel
    #
    wa
    @38
    a1i
    @37
    @0
    @1
    @47
    wcel
    #
    wa
    @38
    a1i
    esumsplit
    syl5eqr
    adantr
    @40
    @48
    cpnf
    @45
    cxad
    @40
    @47
    @7
    vx
    c1
    cvv
    @40
    vx
    nfv
    @56
    @0
    @47
    cvv
    wcel
    @39
    @58
    adantr
    @40
    cA
    @44
    cdif
    #
    cfn
    wcel
    #
    @47
    cfn
    wcel
    @40
    @39
    @44
    cfn
    wcel
    #
    @62
    wn
    @0
    @39
    simpr
    @63
    @40
    @44
    cA
    c0
    csn
    #
    cin
    #
    cfn
    @44
    cA
    @43
    vx
    cab
    #
    cin
    @65
    @43
    vx
    cA
    dfrab3
    @66
    @64
    cA
    @66
    @1
    c0
    wceq
    #
    vx
    cab
    @64
    @43
    @67
    vx
    @32
    @43
    @67
    wb
    @33
    @1
    cvv
    hasheq0
    ax-mp
    #
    abbii
    vx
    c0
    df-sn
    eqtr4i
    ineq2i
    eqtri
    @64
    cfn
    wcel
    @65
    @64
    wss
    @65
    cfn
    wcel
    c0
    snfi
    cA
    @64
    inss2
    @64
    @65
    ssfi
    mp2an
    eqeltri
    a1i
    cA
    @44
    difinf
    syl2anc
    @61
    @47
    cfn
    @43
    vx
    cA
    notrab
    eleq1i
    sylnib
    @37
    @40
    @60
    wa
    #
    @38
    a1i
    @69
    @32
    @1
    c0
    wne
    #
    c1
    @7
    cle
    wbr
    @32
    @69
    @33
    a1i
    @69
    @46
    @70
    @69
    @13
    @46
    @69
    @60
    @13
    @46
    wa
    @40
    @60
    simpr
    @46
    vx
    cA
    rabid
    sylib
    simprd
    @43
    @1
    c0
    @43
    @67
    @68
    biimpri
    necon3bi
    syl
    @1
    cvv
    hashge1
    syl2anc
    c1
    cxr
    wcel
    @40
    c1
    1re
    rexri
    a1i
    cc0
    c1
    clt
    wbr
    @40
    0lt1
    a1i
    esumpinfsum
    oveq2d
    @40
    @45
    cxr
    wcel
    @45
    cmnf
    wne
    #
    @50
    cpnf
    wceq
    @40
    @36
    cxr
    @45
    cc0
    cpnf
    iccssxr
    @40
    @44
    cvv
    wcel
    #
    @37
    vx
    @44
    wral
    @45
    @36
    wcel
    #
    @0
    @72
    @39
    @57
    adantr
    @40
    @37
    vx
    @44
    @37
    @40
    @59
    wa
    @38
    a1i
    ralrimiva
    @44
    @7
    vx
    cvv
    @55
    esumcl
    syl2anc
    #
    sseldi
    @40
    @73
    @71
    @74
    @45
    xrge0neqmnf
    syl
    @45
    xaddpnf1
    syl2anc
    3eqtrd
    eqtr4d
    adantlr
    pm2.61dan
end
