include "cn.mm"
include "c2.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "cn0.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "nn0uz.mm"
include "nnuz.mm"
include "0zd.mm"
include "1zzd.mm"
include "wcel.mm"
include "wa.mm"
include "2nn0.mm"
include "a1i.mm"
include "nn0mulcl.mm"
include "sylan.mm"
include "nn0p1nn.mm"
include "syl.mm"
include "eqid.mm"
include "fmptd.mm"
include "cfv.mm"
include "clt.mm"
include "nn0red.mm"
include "peano2nn0.mm"
include "syl2an.mm"
include "1red.mm"
include "cr.mm"
include "nn0re.mm"
include "adantl.mm"
include "ltp1d.mm"
include "wb.mm"
include "2re.mm"
include "2pos.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "mpbid.mm"
include "ltadd1dd.mm"
include "wceq.mm"
include "weq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "3brtr4d.mm"
include "crn.mm"
include "cdif.mm"
include "wral.mm"
include "eldifi.mm"
include "cc.mm"
include "simpr.mm"
include "0cnd.mm"
include "wn.mm"
include "wrex.mm"
include "cz.mm"
include "nnz.mm"
include "odd2np1.mm"
include "cle.mm"
include "simprl.mm"
include "cmin.mm"
include "cdiv.mm"
include "nnm1nn0.mm"
include "ad2antlr.mm"
include "nn0ge0d.mm"
include "divge0.mm"
include "syl22anc.mm"
include "simprr.mm"
include "2cn.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "mulcl.mm"
include "sylancr.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eqtr3d.mm"
include "2cnd.mm"
include "wne.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "ex.mm"
include "wi.mm"
include "eqcomd.mm"
include "jcad.mm"
include "reximdv2.mm"
include "sylbid.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "adantr.mm"
include "syld.mm"
include "imp.mm"
include "ifclda.mm"
include "fvmpt2.mm"
include "syl2anc.mm"
include "sylan2.mm"
include "eldif.mm"
include "cvv.mm"
include "vex.mm"
include "cbvmptv.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "syl6ibr.mm"
include "con1d.mm"
include "impr.mm"
include "sylan2b.mm"
include "iftrued.mm"
include "ralrimiva.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfeq1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvral.mm"
include "sylib.mm"
include "r19.21bi.mm"
include "ffvelrnda.mm"
include "fveq2d.mm"
include "2z.mm"
include "nn0z.mm"
include "dvdsmul1.mm"
include "nn0zd.mm"
include "2nn.mm"
include "1lt2.mm"
include "ndvdsp1.mm"
include "syl3anc.mm"
include "mpd.mm"
include "iffalsed.mm"
include "eqeltrd.mm"
include "breq2.mm"
include "ifbieq2d.mm"
include "fvmptg.mm"
include "3eqtrd.mm"
include "eqtr4d.mm"
include "eqeq12d.mm"
include "isercoll2.mm"

theorem iserodd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vn: setvar n
  let vi: setvar i
  let vj: setvar j
  let vm: setvar m
  assume iserodd.f: |- ( ( ph /\ k e. NN0 ) -> C e. CC )
  assume iserodd.h: |- ( n = ( ( 2 x. k ) + 1 ) -> B = C )

  disjoint B k
  disjoint C n
  disjoint k n
  disjoint k ph
  disjoint n ph
  disjoint i j
  disjoint A i
  disjoint A j
  disjoint i k
  disjoint B i
  disjoint j k
  disjoint B j
  disjoint i n
  disjoint C i
  disjoint j n
  disjoint C j
  disjoint i m
  disjoint i ph
  disjoint j m
  disjoint j ph
  disjoint k m
  disjoint m n
  disjoint m ph
  assert |- ( ph -> ( seq 0 ( + , ( k e. NN0 |-> C ) ) ~~> A <-> seq 1 ( + , ( n e. NN |-> if ( 2 || n , 0 , B ) ) ) ~~> A ) )

  proof
    wph
    cA
    vi
    vj
    vn
    cn
    c2
    vn
    cv
    #
    cdvds
    wbr
    #
    cc0
    cB
    cif
    #
    cmpt
    #
    vm
    cn0
    c2
    vm
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    cmpt
    #
    vk
    cn0
    cC
    cmpt
    #
    cc0
    c1
    cn
    cn0
    nn0uz
    nnuz
    wph
    0zd
    wph
    1zzd
    wph
    vm
    cn0
    @6
    cn
    @7
    wph
    @4
    cn0
    wcel
    #
    wa
    @5
    cn0
    wcel
    #
    @6
    cn
    wcel
    wph
    c2
    cn0
    wcel
    #
    @9
    @10
    @11
    wph
    2nn0
    a1i
    #
    c2
    @4
    nn0mulcl
    sylan
    @5
    nn0p1nn
    syl
    @7
    eqid
    #
    fmptd
    wph
    vi
    cv
    #
    cn0
    wcel
    #
    wa
    #
    c2
    @14
    cmul
    co
    #
    c1
    caddc
    co
    #
    c2
    @14
    c1
    caddc
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @14
    @7
    cfv
    #
    @19
    @7
    cfv
    #
    clt
    @16
    @17
    @20
    c1
    @16
    @17
    wph
    @11
    @15
    @17
    cn0
    wcel
    @12
    c2
    @14
    nn0mulcl
    sylan
    nn0red
    @16
    @20
    wph
    @11
    @19
    cn0
    wcel
    #
    @20
    cn0
    wcel
    @15
    @12
    @14
    peano2nn0
    #
    c2
    @19
    nn0mulcl
    syl2an
    nn0red
    @16
    1red
    @16
    @14
    @19
    clt
    wbr
    #
    @17
    @20
    clt
    wbr
    #
    @16
    @14
    @15
    @14
    cr
    wcel
    #
    wph
    @14
    nn0re
    adantl
    #
    ltp1d
    @16
    @28
    @19
    cr
    wcel
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    @26
    @27
    wb
    @29
    @16
    @19
    @15
    @24
    wph
    @25
    adantl
    #
    nn0red
    @30
    @16
    2re
    a1i
    @31
    @16
    2pos
    a1i
    @14
    @19
    c2
    ltmul2
    syl112anc
    mpbid
    ltadd1dd
    @15
    @22
    @18
    wceq
    wph
    vm
    @14
    @6
    @18
    cn0
    @7
    vm
    vi
    weq
    @5
    @17
    c1
    caddc
    @4
    @14
    c2
    cmul
    oveq2
    oveq1d
    @13
    @17
    c1
    caddc
    ovex
    fvmpt
    adantl
    @16
    @24
    @23
    @21
    wceq
    @32
    vm
    @19
    @6
    @21
    cn0
    @7
    @4
    @19
    wceq
    @5
    @20
    c1
    caddc
    @4
    @19
    c2
    cmul
    oveq2
    oveq1d
    @13
    @20
    c1
    caddc
    ovex
    fvmpt
    syl
    3brtr4d
    wph
    vj
    cv
    #
    @3
    cfv
    #
    cc0
    wceq
    #
    vj
    cn
    @7
    crn
    #
    cdif
    #
    wph
    @0
    @3
    cfv
    #
    cc0
    wceq
    #
    vn
    @37
    wral
    @35
    vj
    @37
    wral
    wph
    @39
    vn
    @37
    wph
    @0
    @37
    wcel
    #
    wa
    #
    @38
    @2
    cc0
    @40
    wph
    @0
    cn
    wcel
    #
    @38
    @2
    wceq
    #
    @0
    cn
    @36
    eldifi
    wph
    @42
    wa
    #
    @42
    @2
    cc
    wcel
    @43
    wph
    @42
    simpr
    @44
    @1
    cc0
    cB
    cc
    @44
    @1
    wa
    0cnd
    @44
    @1
    wn
    #
    cB
    cc
    wcel
    #
    @44
    @45
    @0
    c2
    vk
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    wceq
    #
    vk
    cn0
    wrex
    #
    @46
    @44
    @45
    @49
    @0
    wceq
    #
    vk
    cz
    wrex
    #
    @51
    @44
    @0
    cz
    wcel
    #
    @45
    @53
    wb
    @42
    @54
    wph
    @0
    nnz
    adantl
    vk
    @0
    odd2np1
    syl
    @44
    @52
    @50
    vk
    cz
    cn0
    @44
    @47
    cz
    wcel
    #
    @52
    wa
    #
    @47
    cn0
    wcel
    #
    @50
    @44
    @56
    @57
    @44
    @56
    wa
    #
    @55
    cc0
    @47
    cle
    wbr
    @57
    @44
    @55
    @52
    simprl
    @58
    cc0
    @0
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    @47
    cle
    @58
    @59
    cr
    wcel
    cc0
    @59
    cle
    wbr
    @30
    @31
    cc0
    @60
    cle
    wbr
    @58
    @59
    @42
    @59
    cn0
    wcel
    wph
    @56
    @0
    nnm1nn0
    ad2antlr
    #
    nn0red
    @58
    @59
    @61
    nn0ge0d
    @30
    @58
    2re
    a1i
    @31
    @58
    2pos
    a1i
    @59
    c2
    divge0
    syl22anc
    @58
    @60
    @48
    c2
    cdiv
    co
    @47
    @58
    @59
    @48
    c2
    cdiv
    @58
    @49
    c1
    cmin
    co
    #
    @59
    @48
    @58
    @49
    @0
    c1
    cmin
    @44
    @55
    @52
    simprr
    oveq1d
    @58
    @48
    cc
    wcel
    #
    c1
    cc
    wcel
    @62
    @48
    wceq
    @58
    c2
    cc
    wcel
    @47
    cc
    wcel
    #
    @63
    2cn
    @55
    @64
    @44
    @52
    @47
    zcn
    ad2antrl
    #
    c2
    @47
    mulcl
    sylancr
    ax-1cn
    @48
    c1
    pncan
    sylancl
    eqtr3d
    oveq1d
    @58
    @47
    c2
    @65
    @58
    2cnd
    c2
    cc0
    wne
    @58
    2ne0
    a1i
    divcan3d
    eqtrd
    breqtrd
    @47
    elnn0z
    sylanbrc
    ex
    @56
    @50
    wi
    @44
    @56
    @49
    @0
    @55
    @52
    simpr
    eqcomd
    a1i
    jcad
    reximdv2
    sylbid
    #
    wph
    @51
    @46
    wi
    @42
    wph
    @50
    @46
    vk
    cn0
    wph
    @57
    wa
    #
    @46
    @50
    cC
    cc
    wcel
    #
    iserodd.f
    @50
    cB
    cC
    cc
    iserodd.h
    eleq1d
    syl5ibrcom
    rexlimdva
    adantr
    syld
    imp
    ifclda
    #
    vn
    cn
    @2
    cc
    @3
    @3
    eqid
    #
    fvmpt2
    syl2anc
    sylan2
    @41
    @1
    cc0
    cB
    @40
    wph
    @42
    @0
    @36
    wcel
    #
    wn
    #
    wa
    @1
    @0
    cn
    @36
    eldif
    wph
    @42
    @72
    @1
    @44
    @1
    @71
    @44
    @45
    @51
    @71
    @66
    @0
    cvv
    wcel
    @71
    @51
    wb
    vn
    vex
    vk
    cn0
    @49
    @0
    @7
    cvv
    vm
    vk
    cn0
    @6
    @49
    vm
    vk
    weq
    @5
    @48
    c1
    caddc
    @4
    @47
    c2
    cmul
    oveq2
    oveq1d
    #
    cbvmptv
    elrnmpt
    ax-mp
    syl6ibr
    con1d
    impr
    sylan2b
    iftrued
    eqtrd
    ralrimiva
    @39
    @35
    vn
    vj
    @37
    @39
    vj
    nfv
    vn
    @34
    cc0
    vn
    cn
    @2
    @33
    nffvmpt1
    nfeq1
    vn
    vj
    weq
    @38
    @34
    cc0
    @0
    @33
    @3
    fveq2
    eqeq1d
    cbvral
    sylib
    r19.21bi
    wph
    cn
    cc
    @33
    @3
    wph
    vn
    cn
    @2
    cc
    @3
    @69
    @70
    fmptd
    ffvelrnda
    wph
    @14
    @8
    cfv
    #
    @22
    @3
    cfv
    #
    wceq
    #
    vi
    cn0
    wph
    @47
    @8
    cfv
    #
    @47
    @7
    cfv
    #
    @3
    cfv
    #
    wceq
    #
    vk
    cn0
    wral
    @76
    vi
    cn0
    wral
    wph
    @80
    vk
    cn0
    @67
    @77
    cC
    @79
    @67
    @57
    @68
    @77
    cC
    wceq
    wph
    @57
    simpr
    iserodd.f
    vk
    cn0
    cC
    cc
    @8
    @8
    eqid
    fvmpt2
    syl2anc
    @67
    @79
    @49
    @3
    cfv
    #
    c2
    @49
    cdvds
    wbr
    #
    cc0
    cC
    cif
    #
    cC
    @67
    @78
    @49
    @3
    @57
    @78
    @49
    wceq
    wph
    vm
    @47
    @6
    @49
    cn0
    @7
    @73
    @13
    @48
    c1
    caddc
    ovex
    fvmpt
    adantl
    fveq2d
    @67
    @49
    cn
    wcel
    #
    @83
    cc
    wcel
    @81
    @83
    wceq
    @67
    @48
    cn0
    wcel
    #
    @84
    wph
    @11
    @57
    @85
    @12
    c2
    @47
    nn0mulcl
    sylan
    #
    @48
    nn0p1nn
    syl
    @67
    @83
    cC
    cc
    @67
    @82
    cc0
    cC
    @67
    c2
    @48
    cdvds
    wbr
    #
    @82
    wn
    #
    @67
    c2
    cz
    wcel
    @55
    @87
    2z
    @57
    @55
    wph
    @47
    nn0z
    adantl
    c2
    @47
    dvdsmul1
    sylancr
    @67
    @48
    cz
    wcel
    c2
    cn
    wcel
    #
    c1
    c2
    clt
    wbr
    #
    @87
    @88
    wi
    @67
    @48
    @86
    nn0zd
    @89
    @67
    2nn
    a1i
    @90
    @67
    1lt2
    a1i
    c2
    @48
    ndvdsp1
    syl3anc
    mpd
    iffalsed
    #
    iserodd.f
    eqeltrd
    vn
    @49
    @2
    @83
    cn
    cc
    @3
    @50
    @1
    @82
    cB
    cC
    cc0
    @0
    @49
    c2
    cdvds
    breq2
    iserodd.h
    ifbieq2d
    @70
    fvmptg
    syl2anc
    @91
    3eqtrd
    eqtr4d
    ralrimiva
    @80
    @76
    vk
    vi
    cn0
    @80
    vi
    nfv
    vk
    @74
    @75
    vk
    cn0
    cC
    @14
    nffvmpt1
    nfeq1
    vk
    vi
    weq
    #
    @77
    @74
    @79
    @75
    @47
    @14
    @8
    fveq2
    @92
    @78
    @22
    @3
    @47
    @14
    @7
    fveq2
    fveq2d
    eqeq12d
    cbvral
    sylib
    r19.21bi
    isercoll2
end
