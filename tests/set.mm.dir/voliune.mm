include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cn.mm"
include "wral.mm"
include "wdisj.mm"
include "wa.mm"
include "cfv.mm"
include "cr.mm"
include "ciun.mm"
include "cesum.mm"
include "wceq.mm"
include "cpnf.mm"
include "wrex.mm"
include "caddc.mm"
include "cmpt.mm"
include "c1.mm"
include "cseq.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "r19.26.mm"
include "eqid.mm"
include "voliun.mm"
include "sylanbr.mm"
include "an32s.mm"
include "cv.mm"
include "nfra1.mm"
include "nfan.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "simpr.mm"
include "rspa.mm"
include "volf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "adantlr.mm"
include "ex.mm"
include "ralrimi.mm"
include "esumeq2d.mm"
include "cico.mm"
include "wf.mm"
include "cle.mm"
include "wbr.mm"
include "r19.21bi.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicc1.mm"
include "mp2an.mm"
include "simp2bi.mm"
include "ltpnf.mm"
include "0re.mm"
include "elico2.mm"
include "syl3anbrc.mm"
include "fmptdf.mm"
include "nfmpt1.mm"
include "esumfsupre.mm"
include "eqtr3d.mm"
include "eqtr4d.mm"
include "csb.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nffv.mm"
include "nfeq1.mm"
include "weq.mm"
include "csbeq1a.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "cbvrex.mm"
include "sylib.mm"
include "wss.mm"
include "nfel1.mm"
include "eleq1d.mm"
include "rspc.mm"
include "impcom.mm"
include "iunmbl.mm"
include "adantr.mm"
include "ssiun2sf.mm"
include "adantl.mm"
include "volss.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "r19.29r.mm"
include "breq1.mm"
include "biimpa.mm"
include "reximi.mm"
include "c0.mm"
include "wne.mm"
include "1nn.mm"
include "ne0i.mm"
include "r19.9rzv.mm"
include "mp2b.mm"
include "sylibr.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "ad2antrr.mm"
include "xgepnf.mm"
include "mpbid.mm"
include "cvv.mm"
include "nfdisj1.mm"
include "nfre1.mm"
include "nnex.mm"
include "a1i.mm"
include "3ad2antr3.mm"
include "3anassrs.mm"
include "esumpinfval.mm"
include "wo.mm"
include "wn.mm"
include "exmid.mm"
include "rexnal.mm"
include "orbi2i.mm"
include "mpbir.mm"
include "r19.29.mm"
include "xrge0nre.mm"
include "sylan.mm"
include "orim2d.mm"
include "mpi.mm"
include "mpjaodan.mm"

theorem voliune
  let cA: class A
  let vn: setvar n
  let vk: setvar k


  assert |- ( ( A. n e. NN A e. dom vol /\ Disj_ n e. NN A ) -> ( vol ` U_ n e. NN A ) = sum* n e. NN ( vol ` A ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    vn
    cn
    wral
    #
    vn
    cn
    cA
    wdisj
    #
    wa
    #
    cA
    cvol
    cfv
    #
    cr
    wcel
    #
    vn
    cn
    wral
    #
    vn
    cn
    cA
    ciun
    #
    cvol
    cfv
    #
    cn
    @5
    vn
    cesum
    #
    wceq
    @5
    cpnf
    wceq
    #
    vn
    cn
    wrex
    #
    @4
    @7
    wa
    @9
    caddc
    vn
    cn
    @5
    cmpt
    #
    c1
    cseq
    #
    crn
    cxr
    clt
    csup
    #
    @10
    @2
    @7
    @3
    @9
    @15
    wceq
    #
    @2
    @7
    wa
    #
    @1
    @6
    wa
    vn
    cn
    wral
    @3
    @16
    @1
    @6
    vn
    cn
    r19.26
    cA
    @14
    vn
    @13
    @14
    eqid
    @13
    eqid
    #
    voliun
    sylanbr
    an32s
    @2
    @7
    @10
    @15
    wceq
    @3
    @17
    cn
    vn
    cv
    #
    @13
    cfv
    #
    vn
    cesum
    #
    @10
    @15
    @17
    cn
    @20
    @5
    vn
    @2
    @7
    vn
    @1
    vn
    cn
    nfra1
    #
    @6
    vn
    cn
    nfra1
    nfan
    #
    @17
    @20
    @5
    wceq
    #
    vn
    cn
    @23
    @17
    @19
    cn
    wcel
    #
    @24
    @2
    @25
    @24
    @7
    @2
    @25
    wa
    #
    @25
    @5
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @24
    @2
    @25
    simpr
    @26
    @1
    @28
    @1
    vn
    cn
    rspa
    @0
    @27
    cA
    cvol
    volf
    ffvelrni
    #
    syl
    #
    vn
    cn
    @5
    @27
    @13
    @18
    fvmpt2
    syl2anc
    adantlr
    ex
    ralrimi
    esumeq2d
    @17
    cn
    cc0
    cpnf
    cico
    co
    #
    @13
    wf
    @21
    @15
    wceq
    @17
    vn
    cn
    @5
    @31
    @13
    @23
    @17
    @25
    wa
    #
    @6
    cc0
    @5
    cle
    wbr
    #
    @5
    cpnf
    clt
    wbr
    #
    @5
    @31
    wcel
    #
    @17
    @6
    vn
    cn
    @2
    @7
    simpr
    r19.21bi
    #
    @32
    @28
    @33
    @2
    @25
    @28
    @7
    @30
    adantlr
    @28
    @5
    cxr
    wcel
    #
    @33
    @5
    cpnf
    cle
    wbr
    #
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    #
    @28
    @37
    @33
    @38
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @5
    elicc1
    mp2an
    simp2bi
    syl
    @32
    @6
    @34
    @36
    @5
    ltpnf
    syl
    cc0
    cr
    wcel
    @39
    @35
    @6
    @33
    @34
    w3a
    wb
    0re
    pnfxr
    cc0
    cpnf
    @5
    elico2
    mp2an
    syl3anbrc
    @18
    fmptdf
    vn
    @13
    vn
    cn
    @5
    nfmpt1
    esumfsupre
    syl
    eqtr3d
    adantlr
    eqtr4d
    @4
    @12
    wa
    #
    @9
    cpnf
    @10
    @40
    cpnf
    @9
    cle
    wbr
    #
    @9
    cpnf
    wceq
    #
    @40
    @41
    vk
    cn
    wrex
    #
    @41
    @40
    vn
    vk
    cv
    #
    cA
    csb
    #
    cvol
    cfv
    #
    cpnf
    wceq
    #
    @46
    @9
    cle
    wbr
    #
    wa
    #
    vk
    cn
    wrex
    #
    @43
    @40
    @47
    vk
    cn
    wrex
    #
    @48
    vk
    cn
    wral
    @50
    @40
    @12
    @51
    @4
    @12
    simpr
    #
    @11
    @47
    vn
    vk
    cn
    @11
    vk
    nfv
    vn
    @46
    cpnf
    vn
    @45
    cvol
    vn
    cvol
    nfcv
    vn
    @44
    cA
    nfcsb1v
    #
    nffv
    nfeq1
    vn
    vk
    weq
    #
    @5
    @46
    cpnf
    @54
    cA
    @45
    cvol
    vn
    @44
    cA
    csbeq1a
    #
    fveq2d
    eqeq1d
    cbvrex
    sylib
    @40
    @48
    vk
    cn
    @4
    @44
    cn
    wcel
    #
    @48
    @12
    @2
    @56
    @48
    @3
    @2
    @56
    wa
    @45
    @0
    wcel
    #
    @8
    @0
    wcel
    #
    @45
    @8
    wss
    #
    @48
    @56
    @2
    @57
    @1
    @57
    vn
    @44
    cn
    vn
    @45
    @0
    @53
    nfel1
    @54
    cA
    @45
    @0
    @55
    eleq1d
    rspc
    impcom
    @2
    @58
    @56
    cA
    vn
    iunmbl
    #
    adantr
    @56
    @59
    @2
    vn
    cn
    cA
    @44
    @45
    vn
    cn
    nfcv
    vn
    @44
    nfcv
    @53
    @55
    ssiun2sf
    adantl
    @45
    @8
    volss
    syl3anc
    adantlr
    adantlr
    ralrimiva
    @47
    @48
    vk
    cn
    r19.29r
    syl2anc
    @49
    @41
    vk
    cn
    @47
    @48
    @41
    @46
    cpnf
    @9
    cle
    breq1
    biimpa
    reximi
    syl
    c1
    cn
    wcel
    cn
    c0
    wne
    @41
    @43
    wb
    1nn
    cn
    c1
    ne0i
    @41
    vk
    cn
    r19.9rzv
    mp2b
    sylibr
    @40
    @9
    cxr
    wcel
    #
    @41
    @42
    wb
    @2
    @61
    @3
    @12
    @2
    @58
    @61
    @60
    @58
    @27
    cxr
    @9
    cc0
    cpnf
    iccssxr
    @0
    @27
    @8
    cvol
    volf
    ffvelrni
    sseldi
    syl
    ad2antrr
    @9
    xgepnf
    syl
    mpbid
    @40
    cn
    @5
    vn
    cvv
    @4
    @12
    vn
    @2
    @3
    vn
    @22
    vn
    cn
    cA
    nfdisj1
    nfan
    @11
    vn
    cn
    nfre1
    nfan
    cn
    cvv
    wcel
    @40
    nnex
    a1i
    @2
    @3
    @12
    @25
    @28
    @2
    @3
    @25
    @28
    @12
    @30
    3ad2antr3
    3anassrs
    @52
    esumpinfval
    eqtr4d
    @2
    @7
    @12
    wo
    #
    @3
    @2
    @7
    @6
    wn
    #
    vn
    cn
    wrex
    #
    wo
    #
    @62
    @65
    @7
    @7
    wn
    #
    wo
    @7
    exmid
    @64
    @66
    @7
    @6
    vn
    cn
    rexnal
    orbi2i
    mpbir
    @2
    @64
    @12
    @7
    @2
    @64
    @12
    @2
    @64
    wa
    @1
    @63
    wa
    #
    vn
    cn
    wrex
    @12
    @1
    @63
    vn
    cn
    r19.29
    @67
    @11
    vn
    cn
    @1
    @28
    @63
    @11
    @29
    @5
    xrge0nre
    sylan
    reximi
    syl
    ex
    orim2d
    mpi
    adantr
    mpjaodan
end
