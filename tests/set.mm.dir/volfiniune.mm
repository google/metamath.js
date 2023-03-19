include "cfn.mm"
include "wcel.mm"
include "cvol.mm"
include "cdm.mm"
include "wral.mm"
include "wdisj.mm"
include "w3a.mm"
include "cfv.mm"
include "cr.mm"
include "ciun.mm"
include "cesum.mm"
include "wceq.mm"
include "cpnf.mm"
include "wrex.mm"
include "wa.mm"
include "csu.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "r19.26.mm"
include "sylanbrc.mm"
include "simpl3.mm"
include "volfiniun.mm"
include "syl3anc.mm"
include "nfcv.mm"
include "nfel1.mm"
include "nfra1.mm"
include "nfdisj1.mm"
include "nf3an.mm"
include "nfan.mm"
include "cv.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "cico.mm"
include "co.mm"
include "r19.21bi.mm"
include "cicc.mm"
include "rspa.mm"
include "volf.mm"
include "ffvelrni.mm"
include "syl.mm"
include "sylan.mm"
include "cxr.mm"
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
include "esumpfinvalf.mm"
include "eqtr4d.mm"
include "csb.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nffv.mm"
include "nfeq1.mm"
include "csbeq1a.mm"
include "fveq2d.mm"
include "eqeq1d.mm"
include "cbvrex.mm"
include "sylib.mm"
include "wss.mm"
include "eleq1d.mm"
include "rspc.mm"
include "impcom.mm"
include "adantll.mm"
include "finiunmbl.mm"
include "adantr.mm"
include "ssiun2sf.mm"
include "adantl.mm"
include "volss.mm"
include "3adantl3.mm"
include "adantlr.mm"
include "ralrimiva.mm"
include "r19.29r.mm"
include "syl2anc.mm"
include "breq1.mm"
include "biimpa.mm"
include "reximi.mm"
include "wex.mm"
include "rexex.mm"
include "19.9v.mm"
include "iccssxr.mm"
include "sseldi.mm"
include "3adant3.mm"
include "xgepnf.mm"
include "mpbid.mm"
include "nfre1.mm"
include "3ad2antl2.mm"
include "esumpinfval.mm"
include "wo.mm"
include "wn.mm"
include "exmid.mm"
include "rexnal.mm"
include "orbi2i.mm"
include "mpbir.mm"
include "r19.29.mm"
include "xrge0nre.mm"
include "ex.mm"
include "orim2d.mm"
include "mpi.mm"
include "3ad2ant2.mm"
include "mpjaodan.mm"

theorem volfiniune
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vk: setvar k

  disjoint A n
  disjoint k n
  disjoint A k
  disjoint B k
  assert |- ( ( A e. Fin /\ A. n e. A B e. dom vol /\ Disj_ n e. A B ) -> ( vol ` U_ n e. A B ) = sum* n e. A ( vol ` B ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cvol
    cdm
    #
    wcel
    #
    vn
    cA
    wral
    #
    vn
    cA
    cB
    wdisj
    #
    w3a
    #
    cB
    cvol
    cfv
    #
    cr
    wcel
    #
    vn
    cA
    wral
    #
    vn
    cA
    cB
    ciun
    #
    cvol
    cfv
    #
    cA
    @6
    vn
    cesum
    #
    wceq
    @6
    cpnf
    wceq
    #
    vn
    cA
    wrex
    #
    @5
    @8
    wa
    #
    @10
    cA
    @6
    vn
    csu
    #
    @11
    @14
    @0
    @2
    @7
    wa
    vn
    cA
    wral
    #
    @4
    @10
    @15
    wceq
    @0
    @3
    @4
    @8
    simpl1
    #
    @14
    @3
    @8
    @16
    @0
    @3
    @4
    @8
    simpl2
    #
    @5
    @8
    simpr
    #
    @2
    @7
    vn
    cA
    r19.26
    sylanbrc
    @0
    @3
    @4
    @8
    simpl3
    cA
    cB
    vn
    volfiniun
    syl3anc
    @14
    cA
    @6
    vn
    vn
    cA
    nfcv
    #
    @5
    @8
    vn
    @0
    @3
    @4
    vn
    vn
    cA
    cfn
    @20
    nfel1
    @2
    vn
    cA
    nfra1
    vn
    cA
    cB
    nfdisj1
    nf3an
    #
    @7
    vn
    cA
    nfra1
    nfan
    @17
    @14
    vn
    cv
    #
    cA
    wcel
    #
    wa
    #
    @7
    cc0
    @6
    cle
    wbr
    #
    @6
    cpnf
    clt
    wbr
    #
    @6
    cc0
    cpnf
    cico
    co
    wcel
    #
    @14
    @7
    vn
    cA
    @19
    r19.21bi
    #
    @24
    @6
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    @25
    @14
    @3
    @23
    @30
    @18
    @3
    @23
    wa
    @2
    @30
    @2
    vn
    cA
    rspa
    @1
    @29
    cB
    cvol
    volf
    ffvelrni
    #
    syl
    #
    sylan
    @30
    @6
    cxr
    wcel
    #
    @25
    @6
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
    @30
    @33
    @25
    @34
    w3a
    wb
    0xr
    pnfxr
    cc0
    cpnf
    @6
    elicc1
    mp2an
    simp2bi
    syl
    @24
    @7
    @26
    @28
    @6
    ltpnf
    syl
    cc0
    cr
    wcel
    @35
    @27
    @7
    @25
    @26
    w3a
    wb
    0re
    pnfxr
    cc0
    cpnf
    @6
    elico2
    mp2an
    syl3anbrc
    esumpfinvalf
    eqtr4d
    @5
    @13
    wa
    #
    @10
    cpnf
    @11
    @36
    cpnf
    @10
    cle
    wbr
    #
    @10
    cpnf
    wceq
    #
    @36
    @37
    vk
    cA
    wrex
    #
    @37
    @36
    vn
    vk
    cv
    #
    cB
    csb
    #
    cvol
    cfv
    #
    cpnf
    wceq
    #
    @42
    @10
    cle
    wbr
    #
    wa
    #
    vk
    cA
    wrex
    #
    @39
    @36
    @43
    vk
    cA
    wrex
    #
    @44
    vk
    cA
    wral
    @46
    @36
    @13
    @47
    @5
    @13
    simpr
    #
    @12
    @43
    vn
    vk
    cA
    @12
    vk
    nfv
    vn
    @42
    cpnf
    vn
    @41
    cvol
    vn
    cvol
    nfcv
    vn
    @40
    cB
    nfcsb1v
    #
    nffv
    nfeq1
    @22
    @40
    wceq
    #
    @6
    @42
    cpnf
    @50
    cB
    @41
    cvol
    vn
    @40
    cB
    csbeq1a
    #
    fveq2d
    eqeq1d
    cbvrex
    sylib
    @36
    @44
    vk
    cA
    @5
    @40
    cA
    wcel
    #
    @44
    @13
    @0
    @3
    @52
    @44
    @4
    @0
    @3
    wa
    #
    @52
    wa
    @41
    @1
    wcel
    #
    @9
    @1
    wcel
    #
    @41
    @9
    wss
    #
    @44
    @3
    @52
    @54
    @0
    @52
    @3
    @54
    @2
    @54
    vn
    @40
    cA
    vn
    @41
    @1
    @49
    nfel1
    @50
    cB
    @41
    @1
    @51
    eleq1d
    rspc
    impcom
    adantll
    @53
    @55
    @52
    cA
    cB
    vn
    finiunmbl
    #
    adantr
    @52
    @56
    @53
    vn
    cA
    cB
    @40
    @41
    @20
    vn
    @40
    nfcv
    @49
    @51
    ssiun2sf
    adantl
    @41
    @9
    volss
    syl3anc
    3adantl3
    adantlr
    ralrimiva
    @43
    @44
    vk
    cA
    r19.29r
    syl2anc
    @45
    @37
    vk
    cA
    @43
    @44
    @37
    @42
    cpnf
    @10
    cle
    breq1
    biimpa
    reximi
    syl
    @39
    @37
    vk
    wex
    @37
    @37
    vk
    cA
    rexex
    @37
    vk
    19.9v
    sylib
    syl
    @36
    @10
    cxr
    wcel
    #
    @37
    @38
    wb
    @5
    @58
    @13
    @0
    @3
    @58
    @4
    @53
    @55
    @58
    @57
    @55
    @29
    cxr
    @10
    cc0
    cpnf
    iccssxr
    @1
    @29
    @9
    cvol
    volf
    ffvelrni
    sseldi
    syl
    3adant3
    adantr
    @10
    xgepnf
    syl
    mpbid
    @36
    cA
    @6
    vn
    cfn
    @5
    @13
    vn
    @21
    @12
    vn
    cA
    nfre1
    nfan
    @0
    @3
    @4
    @13
    simpl1
    @5
    @23
    @30
    @13
    @3
    @0
    @23
    @30
    @4
    @32
    3ad2antl2
    adantlr
    @48
    esumpinfval
    eqtr4d
    @3
    @0
    @8
    @13
    wo
    #
    @4
    @3
    @8
    @7
    wn
    #
    vn
    cA
    wrex
    #
    wo
    #
    @59
    @62
    @8
    @8
    wn
    #
    wo
    @8
    exmid
    @61
    @63
    @8
    @7
    vn
    cA
    rexnal
    orbi2i
    mpbir
    @3
    @61
    @13
    @8
    @3
    @61
    @13
    @3
    @61
    wa
    @2
    @60
    wa
    #
    vn
    cA
    wrex
    @13
    @2
    @60
    vn
    cA
    r19.29
    @64
    @12
    vn
    cA
    @2
    @30
    @60
    @12
    @31
    @6
    xrge0nre
    sylan
    reximi
    syl
    ex
    orim2d
    mpi
    3ad2ant2
    mpjaodan
end
