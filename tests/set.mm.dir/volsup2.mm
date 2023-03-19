include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cv.mm"
include "cneg.mm"
include "cicc.mm"
include "co.mm"
include "cin.mm"
include "cn.mm"
include "wrex.mm"
include "cle.mm"
include "wn.mm"
include "wral.mm"
include "simp3.mm"
include "cxr.mm"
include "wb.mm"
include "rexr.mm"
include "3ad2ant2.mm"
include "cc0.mm"
include "cpnf.mm"
include "iccssxr.mm"
include "volf.mm"
include "ffvelrni.mm"
include "sseldi.mm"
include "3ad2ant1.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "cmpt.mm"
include "crn.mm"
include "cima.mm"
include "csup.mm"
include "cuni.mm"
include "ciun.mm"
include "wceq.mm"
include "negeq.mm"
include "id.mm"
include "oveq12d.mm"
include "ineq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "inex2.mm"
include "fvmpt.mm"
include "iuneq2i.mm"
include "iunin2.mm"
include "eqtri.mm"
include "wfn.mm"
include "wf.mm"
include "wa.mm"
include "simpl1.mm"
include "nnre.mm"
include "adantl.mm"
include "renegcld.mm"
include "iccmbl.mm"
include "inmbl.mm"
include "cbvmptv.mm"
include "fmptd.mm"
include "ffn.mm"
include "syl.mm"
include "fniunfv.mm"
include "wss.mm"
include "mblss.mm"
include "sselda.mm"
include "cabs.mm"
include "recn.mm"
include "abscld.mm"
include "arch.mm"
include "wi.mm"
include "ltle.mm"
include "syl2an.mm"
include "3expib.mm"
include "adantr.mm"
include "absle.mm"
include "sylan2.mm"
include "elicc2.mm"
include "3imtr4d.mm"
include "syld.mm"
include "reximdva.mm"
include "mpd.mm"
include "ex.mm"
include "eliun.mm"
include "syl6ibr.mm"
include "ssrdv.mm"
include "df-ss.mm"
include "sylib.mm"
include "3eqtr3a.mm"
include "fveq2d.mm"
include "c1.mm"
include "caddc.mm"
include "peano2re.mm"
include "lep1d.mm"
include "lenegd.mm"
include "iccss.mm"
include "syl22anc.mm"
include "sslin.mm"
include "peano2nn.mm"
include "3sstr4d.mm"
include "ralrimiva.mm"
include "volsup.mm"
include "eqtr3d.mm"
include "breq1d.mm"
include "imassrn.mm"
include "frn.mm"
include "ax-mp.mm"
include "sstri.mm"
include "supxrleub.mm"
include "sylancr.mm"
include "breq1.mm"
include "ralima.mm"
include "fveq2.mm"
include "ralrn.mm"
include "ralbiia.mm"
include "syl6bb.mm"
include "bitrd.mm"
include "3bitrd.mm"
include "mtbid.mm"
include "rexnal.mm"
include "sylibr.mm"
include "rexbidva.mm"
include "mpbird.mm"

theorem volsup2
  let cA: class A
  let cB: class B
  let vn: setvar n
  let vm: setvar m
  let vx: setvar x
  let vz: setvar z

  disjoint A n
  disjoint B n
  disjoint m n
  disjoint m x
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n z
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  assert |- ( ( A e. dom vol /\ B e. RR /\ B < ( vol ` A ) ) -> E. n e. NN B < ( vol ` ( A i^i ( -u n [,] n ) ) ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    cr
    wcel
    #
    cB
    cA
    cvol
    cfv
    #
    clt
    wbr
    #
    w3a
    #
    cB
    cA
    vn
    cv
    #
    cneg
    #
    @6
    cicc
    co
    #
    cin
    #
    cvol
    cfv
    #
    clt
    wbr
    #
    vn
    cn
    wrex
    @10
    cB
    cle
    wbr
    #
    wn
    #
    vn
    cn
    wrex
    #
    @5
    @12
    vn
    cn
    wral
    #
    wn
    @14
    @5
    @3
    cB
    cle
    wbr
    #
    @15
    @5
    @4
    @16
    wn
    #
    @1
    @2
    @4
    simp3
    @5
    cB
    cxr
    wcel
    #
    @3
    cxr
    wcel
    #
    @4
    @17
    wb
    @2
    @1
    @18
    @4
    cB
    rexr
    3ad2ant2
    #
    @1
    @2
    @19
    @4
    @1
    cc0
    cpnf
    cicc
    co
    #
    cxr
    @3
    cc0
    cpnf
    iccssxr
    #
    @0
    @21
    cA
    cvol
    volf
    ffvelrni
    sseldi
    3ad2ant1
    cB
    @3
    xrltnle
    syl2anc
    mpbid
    @5
    @16
    cvol
    vm
    cn
    cA
    vm
    cv
    #
    cneg
    #
    @23
    cicc
    co
    #
    cin
    #
    cmpt
    #
    crn
    #
    cima
    #
    cxr
    clt
    csup
    #
    cB
    cle
    wbr
    #
    @6
    cB
    cle
    wbr
    #
    vn
    @29
    wral
    #
    @15
    @5
    @3
    @30
    cB
    cle
    @5
    @28
    cuni
    #
    cvol
    cfv
    #
    @3
    @30
    @5
    @34
    cA
    cvol
    @5
    vn
    cn
    @6
    @27
    cfv
    #
    ciun
    #
    cA
    vn
    cn
    @8
    ciun
    #
    cin
    #
    @34
    cA
    @37
    vn
    cn
    @9
    ciun
    @39
    vn
    cn
    @36
    @9
    vm
    @6
    @26
    @9
    cn
    @27
    @23
    @6
    wceq
    #
    @25
    @8
    cA
    @40
    @24
    @7
    @23
    @6
    cicc
    @23
    @6
    negeq
    @40
    id
    oveq12d
    ineq2d
    #
    @27
    eqid
    #
    @8
    cA
    @7
    @6
    cicc
    ovex
    inex2
    fvmpt
    #
    iuneq2i
    vn
    cn
    cA
    @8
    iunin2
    eqtri
    @5
    @27
    cn
    wfn
    #
    @37
    @34
    wceq
    @5
    cn
    @0
    @27
    wf
    #
    @44
    @5
    vn
    cn
    @9
    @0
    @27
    @5
    @6
    cn
    wcel
    #
    wa
    #
    @1
    @8
    @0
    wcel
    #
    @9
    @0
    wcel
    #
    @1
    @2
    @4
    @46
    simpl1
    @47
    @7
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @48
    @47
    @6
    @46
    @51
    @5
    @6
    nnre
    #
    adantl
    #
    renegcld
    @53
    @7
    @6
    iccmbl
    syl2anc
    cA
    @8
    inmbl
    syl2anc
    #
    vm
    vn
    cn
    @26
    @9
    @41
    cbvmptv
    fmptd
    #
    cn
    @0
    @27
    ffn
    syl
    #
    vn
    cn
    @27
    fniunfv
    syl
    @5
    cA
    @38
    wss
    @39
    cA
    wceq
    @5
    vx
    cA
    @38
    @5
    vx
    cv
    #
    cA
    wcel
    #
    @57
    @8
    wcel
    #
    vn
    cn
    wrex
    #
    @57
    @38
    wcel
    @5
    @58
    @60
    @5
    @58
    wa
    @57
    cr
    wcel
    #
    @60
    @5
    cA
    cr
    @57
    @1
    @2
    cA
    cr
    wss
    @4
    cA
    mblss
    3ad2ant1
    sselda
    @61
    @57
    cabs
    cfv
    #
    @6
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @60
    @61
    @62
    cr
    wcel
    #
    @64
    @61
    @57
    @57
    recn
    abscld
    #
    @62
    vn
    arch
    syl
    @61
    @63
    @59
    vn
    cn
    @61
    @46
    wa
    #
    @63
    @62
    @6
    cle
    wbr
    #
    @59
    @61
    @65
    @51
    @63
    @68
    wi
    @46
    @66
    @52
    @62
    @6
    ltle
    syl2an
    @67
    @7
    @57
    cle
    wbr
    #
    @57
    @6
    cle
    wbr
    #
    wa
    #
    @61
    @69
    @70
    w3a
    #
    @68
    @59
    @61
    @71
    @72
    wi
    @46
    @61
    @69
    @70
    @72
    @72
    id
    3expib
    adantr
    @46
    @61
    @51
    @68
    @71
    wb
    @52
    @57
    @6
    absle
    sylan2
    @67
    @50
    @51
    @59
    @72
    wb
    @67
    @6
    @46
    @51
    @61
    @52
    adantl
    #
    renegcld
    @73
    @7
    @6
    @57
    elicc2
    syl2anc
    3imtr4d
    syld
    reximdva
    mpd
    syl
    ex
    vn
    @57
    cn
    @8
    eliun
    syl6ibr
    ssrdv
    cA
    @38
    df-ss
    sylib
    3eqtr3a
    fveq2d
    @5
    @45
    @36
    @6
    c1
    caddc
    co
    #
    @27
    cfv
    #
    wss
    #
    vn
    cn
    wral
    @35
    @30
    wceq
    @55
    @5
    @76
    vn
    cn
    @47
    @9
    cA
    @74
    cneg
    #
    @74
    cicc
    co
    #
    cin
    #
    @36
    @75
    @47
    @8
    @78
    wss
    #
    @9
    @79
    wss
    @47
    @77
    cr
    wcel
    @74
    cr
    wcel
    #
    @77
    @7
    cle
    wbr
    #
    @6
    @74
    cle
    wbr
    #
    @80
    @47
    @74
    @47
    @51
    @81
    @53
    @6
    peano2re
    syl
    #
    renegcld
    @84
    @47
    @83
    @82
    @47
    @6
    @53
    lep1d
    #
    @47
    @6
    @74
    @53
    @84
    lenegd
    mpbid
    @85
    @77
    @74
    @7
    @6
    iccss
    syl22anc
    @8
    @78
    cA
    sslin
    syl
    @46
    @36
    @9
    wceq
    @5
    @43
    adantl
    @47
    @74
    cn
    wcel
    #
    @75
    @79
    wceq
    @46
    @86
    @5
    @6
    peano2nn
    adantl
    vm
    @74
    @26
    @79
    cn
    @27
    @23
    @74
    wceq
    #
    @25
    @78
    cA
    @87
    @24
    @77
    @23
    @74
    cicc
    @23
    @74
    negeq
    @87
    id
    oveq12d
    ineq2d
    @42
    @78
    cA
    @77
    @74
    cicc
    ovex
    inex2
    fvmpt
    syl
    3sstr4d
    ralrimiva
    vn
    @27
    volsup
    syl2anc
    eqtr3d
    breq1d
    @5
    @29
    cxr
    wss
    @18
    @31
    @33
    wb
    @29
    cvol
    crn
    #
    cxr
    cvol
    @28
    imassrn
    @88
    @21
    cxr
    @0
    @21
    cvol
    wf
    #
    @88
    @21
    wss
    volf
    @0
    @21
    cvol
    frn
    ax-mp
    @22
    sstri
    sstri
    @20
    vn
    @29
    cB
    supxrleub
    sylancr
    @5
    @33
    vz
    cv
    #
    cvol
    cfv
    #
    cB
    cle
    wbr
    #
    vz
    @28
    wral
    #
    @15
    @5
    cvol
    @0
    wfn
    #
    @28
    @0
    wss
    #
    @33
    @93
    wb
    @89
    @94
    volf
    @0
    @21
    cvol
    ffn
    ax-mp
    @5
    @45
    @95
    @55
    cn
    @0
    @27
    frn
    syl
    @32
    @92
    vn
    vz
    @0
    @28
    cvol
    @6
    @91
    cB
    cle
    breq1
    ralima
    sylancr
    @5
    @93
    @36
    cvol
    cfv
    #
    cB
    cle
    wbr
    #
    vn
    cn
    wral
    #
    @15
    @5
    @44
    @93
    @98
    wb
    @56
    @92
    @97
    vz
    vn
    cn
    @27
    @90
    @36
    wceq
    @91
    @96
    cB
    cle
    @90
    @36
    cvol
    fveq2
    breq1d
    ralrn
    syl
    @97
    @12
    vn
    cn
    @46
    @96
    @10
    cB
    cle
    @46
    @36
    @9
    cvol
    @43
    fveq2d
    breq1d
    ralbiia
    syl6bb
    bitrd
    3bitrd
    mtbid
    @12
    vn
    cn
    rexnal
    sylibr
    @5
    @11
    @13
    vn
    cn
    @47
    @18
    @10
    cxr
    wcel
    #
    @11
    @13
    wb
    @5
    @18
    @46
    @20
    adantr
    @47
    @49
    @99
    @54
    @49
    @21
    cxr
    @10
    @22
    @0
    @21
    @9
    cvol
    volf
    ffvelrni
    sseldi
    syl
    cB
    @10
    xrltnle
    syl2anc
    rexbidva
    mpbird
end
