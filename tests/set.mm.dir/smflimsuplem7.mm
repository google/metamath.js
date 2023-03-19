include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "clsp.mm"
include "cr.mm"
include "wcel.mm"
include "cuz.mm"
include "cdm.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "cli.mm"
include "wceq.mm"
include "a1i.mm"
include "wb.mm"
include "wal.mm"
include "wa.mm"
include "wrex.mm"
include "simpl.mm"
include "rabidim2.mm"
include "adantl.mm"
include "rabidim1.mm"
include "eliun.mm"
include "sylib.mm"
include "nfv.mm"
include "w3a.mm"
include "wral.mm"
include "nfcv.mm"
include "nfmpt1.mm"
include "nffv.mm"
include "nfel.mm"
include "nfan.mm"
include "nfii1.mm"
include "nf3an.mm"
include "cz.mm"
include "simpl1l.mm"
include "syl.mm"
include "csalg.mm"
include "csmblfn.mm"
include "wf.mm"
include "uztrn2.mm"
include "3ad2antl2.mm"
include "simpl1r.mm"
include "wss.mm"
include "uzss.mm"
include "iinss1.mm"
include "sseldd.mm"
include "3ad2antl3.mm"
include "smflimsuplem2.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "vex.mm"
include "eliin.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "3exp.mm"
include "reximdai.mm"
include "imp.mm"
include "syl21anc.mm"
include "biimpi.mm"
include "nfiu1.mm"
include "nfrab.mm"
include "wi.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2.mm"
include "simp3.mm"
include "smflimsuplem6.mm"
include "syldan.mm"
include "rexlimd.mm"
include "mpd.mm"
include "jca.mm"
include "rabid.mm"
include "ex.mm"
include "ssrab2.mm"
include "eluzelz2.mm"
include "uzidd.mm"
include "wfn.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wor.mm"
include "xrltso.mm"
include "supexd.mm"
include "eqid.mm"
include "fnmptd.mm"
include "fveq2.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "supeq1d.mm"
include "mpteq12dv.mm"
include "fvex.mm"
include "mptex.mm"
include "fvmpt.mm"
include "fneq1d.mm"
include "mpbird.mm"
include "fndmd.mm"
include "iineq1d.mm"
include "eleq2d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rabbidva2.mm"
include "id.mm"
include "mpteq2dv.mm"
include "cbvrabv.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "dmex.mm"
include "rgenw.mm"
include "iinexd.mm"
include "rabexd.mm"
include "fvmptd3.mm"
include "eqsstrd.mm"
include "dmeqd.mm"
include "sseq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "iinss.mm"
include "ss2iun.mm"
include "sstrd.mm"
include "simplbi.mm"
include "simprbi.mm"
include "adantr.mm"
include "3adant3.mm"
include "3adant1r.mm"
include "smflimsuplem4.mm"
include "sylan2.mm"
include "nfrab1.mm"
include "ssrabf.mm"
include "sseld.mm"
include "impbid.mm"
include "alrimiv.mm"
include "dfcleqf.mm"
include "eqtrd.mm"

theorem smflimsuplem7
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cH: class H
  let cM: class M
  let cZ: class Z
  let vy: setvar y
  assume smflimsuplem7.m: |- ( ph -> M e. ZZ )
  assume smflimsuplem7.z: |- Z = ( ZZ>= ` M )
  assume smflimsuplem7.s: |- ( ph -> S e. SAlg )
  assume smflimsuplem7.f: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimsuplem7.d: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( limsup ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) e. RR }
  assume smflimsuplem7.e: |- E = ( k e. Z |-> { x e. |^|_ m e. ( ZZ>= ` k ) dom ( F ` m ) | sup ( ran ( m e. ( ZZ>= ` k ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) e. RR } )
  assume smflimsuplem7.h: |- H = ( k e. Z |-> ( x e. ( E ` k ) |-> sup ( ran ( m e. ( ZZ>= ` k ) |-> ( ( F ` m ) ` x ) ) , RR* , < ) ) )

  disjoint E k
  disjoint E x
  disjoint k x
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint k m
  disjoint k n
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint M m
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint k x
  disjoint F y
  disjoint m y
  disjoint n y
  disjoint x y
  assert |- ( ph -> D = { x e. U_ n e. Z |^|_ k e. ( ZZ>= ` n ) dom ( H ` k ) | ( k e. Z |-> ( ( H ` k ) ` x ) ) e. dom ~~> } )

  proof
    wph
    cD
    vm
    cZ
    vx
    cv
    #
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    clsp
    cfv
    #
    cr
    wcel
    #
    vx
    vn
    cZ
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    @2
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    #
    vk
    cZ
    @0
    vk
    cv
    #
    cH
    cfv
    #
    cfv
    #
    cmpt
    #
    cli
    cdm
    #
    wcel
    #
    vx
    vn
    cZ
    vk
    @8
    @14
    cdm
    #
    ciin
    #
    ciun
    #
    crab
    #
    cD
    @12
    wceq
    wph
    smflimsuplem7.d
    a1i
    wph
    @0
    @12
    wcel
    #
    @0
    @22
    wcel
    #
    wb
    #
    vx
    wal
    @12
    @22
    wceq
    wph
    @25
    vx
    wph
    @23
    @24
    wph
    @23
    @24
    wph
    @23
    wa
    #
    @0
    @21
    wcel
    #
    @18
    wa
    @24
    @26
    @27
    @18
    @26
    wph
    @6
    @0
    @10
    wcel
    #
    vn
    cZ
    wrex
    #
    @27
    wph
    @23
    simpl
    @23
    @6
    wph
    @6
    vx
    @11
    rabidim2
    adantl
    #
    @23
    @29
    wph
    @23
    @0
    @11
    wcel
    #
    @29
    @6
    vx
    @11
    rabidim1
    #
    vn
    @0
    cZ
    @10
    eliun
    #
    sylib
    adantl
    wph
    @6
    wa
    #
    @29
    wa
    @0
    @20
    wcel
    #
    vn
    cZ
    wrex
    #
    @27
    @34
    @29
    @36
    @34
    @28
    @35
    vn
    cZ
    @34
    vn
    nfv
    @34
    @7
    cZ
    wcel
    #
    @28
    @35
    @34
    @37
    @28
    w3a
    #
    @0
    @19
    wcel
    #
    vk
    @8
    wral
    #
    @35
    @38
    @39
    vk
    @8
    @38
    @13
    @8
    wcel
    #
    wa
    #
    vx
    cS
    vm
    vk
    cE
    cF
    cH
    cM
    @0
    cZ
    @38
    @41
    vm
    @34
    @37
    @28
    vm
    wph
    @6
    vm
    wph
    vm
    nfv
    vm
    @5
    cr
    vm
    @4
    clsp
    vm
    clsp
    nfcv
    vm
    cZ
    @3
    nfmpt1
    nffv
    vm
    cr
    nfcv
    nfel
    nfan
    @37
    vm
    nfv
    vm
    @0
    @10
    vm
    @0
    nfcv
    vm
    @8
    @9
    nfii1
    nfel
    nf3an
    #
    @41
    vm
    nfv
    nfan
    @42
    wph
    cM
    cz
    wcel
    #
    wph
    @6
    @37
    @28
    @41
    simpl1l
    #
    smflimsuplem7.m
    syl
    smflimsuplem7.z
    @42
    wph
    cS
    csalg
    wcel
    #
    @45
    smflimsuplem7.s
    syl
    @42
    wph
    cZ
    cS
    csmblfn
    cfv
    cF
    wf
    #
    @45
    smflimsuplem7.f
    syl
    smflimsuplem7.e
    smflimsuplem7.h
    @37
    @34
    @41
    @13
    cZ
    wcel
    @28
    cM
    @13
    @7
    cZ
    smflimsuplem7.z
    uztrn2
    3ad2antl2
    wph
    @6
    @37
    @28
    @41
    simpl1r
    @28
    @34
    @41
    @0
    vm
    @13
    cuz
    cfv
    #
    @9
    ciin
    #
    wcel
    #
    @37
    @28
    @41
    wa
    @10
    @49
    @0
    @41
    @10
    @49
    wss
    #
    @28
    @41
    @48
    @8
    wss
    @51
    @7
    @13
    uzss
    vm
    @48
    @8
    @9
    iinss1
    syl
    adantl
    @28
    @41
    simpl
    sseldd
    3ad2antl3
    smflimsuplem2
    ralrimiva
    @0
    cvv
    wcel
    @35
    @40
    wb
    vx
    vex
    vk
    @0
    @8
    @19
    cvv
    eliin
    ax-mp
    sylibr
    3exp
    reximdai
    imp
    vn
    @0
    cZ
    @20
    eliun
    #
    sylibr
    syl21anc
    @26
    @29
    @18
    @23
    @29
    wph
    @23
    @31
    @29
    @32
    @31
    @29
    @33
    biimpi
    syl
    adantl
    @26
    @28
    @18
    vn
    cZ
    wph
    @23
    vn
    wph
    vn
    nfv
    #
    vn
    @0
    @12
    vn
    @0
    nfcv
    #
    @6
    vn
    vx
    @11
    @6
    vn
    nfv
    #
    vn
    cZ
    @10
    nfiu1
    nfrab
    nfel
    nfan
    @18
    vn
    nfv
    #
    wph
    @23
    @6
    @37
    @28
    @18
    wi
    wi
    @30
    @34
    @37
    @28
    @18
    @38
    vx
    cS
    vm
    vk
    cE
    cF
    cH
    cM
    @7
    @0
    cZ
    @38
    vk
    nfv
    @43
    @38
    wph
    @44
    wph
    @6
    @37
    @28
    simp1l
    #
    smflimsuplem7.m
    syl
    smflimsuplem7.z
    @38
    wph
    @46
    @57
    smflimsuplem7.s
    syl
    @38
    wph
    @47
    @57
    smflimsuplem7.f
    syl
    smflimsuplem7.e
    smflimsuplem7.h
    wph
    @6
    @37
    @28
    simp1r
    @34
    @37
    @28
    simp2
    @34
    @37
    @28
    simp3
    smflimsuplem6
    3exp
    syldan
    rexlimd
    mpd
    jca
    @18
    vx
    @21
    rabid
    #
    sylibr
    ex
    wph
    @22
    @12
    @0
    wph
    @22
    @11
    wss
    #
    @6
    vx
    @22
    wral
    #
    wa
    @22
    @12
    wss
    wph
    @59
    @60
    wph
    @22
    @21
    @11
    @22
    @21
    wss
    wph
    @18
    vx
    @21
    ssrab2
    a1i
    wph
    @20
    @10
    wss
    #
    vn
    cZ
    wral
    @21
    @11
    wss
    wph
    @61
    vn
    cZ
    wph
    @37
    wa
    #
    @19
    @10
    wss
    #
    vk
    @8
    wrex
    #
    @61
    @62
    @7
    @8
    wcel
    #
    @7
    cH
    cfv
    #
    cdm
    #
    @10
    wss
    #
    @64
    @37
    @65
    wph
    @37
    @7
    cM
    @7
    cZ
    smflimsuplem7.z
    eluzelz2
    uzidd
    #
    adantl
    @62
    @67
    @7
    cE
    cfv
    #
    @10
    @62
    @70
    @66
    @62
    @66
    @70
    wfn
    vx
    @70
    vm
    @8
    @3
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    @70
    wfn
    @62
    vx
    @70
    @73
    @74
    cvv
    @62
    vx
    nfv
    @62
    @0
    @70
    wcel
    wa
    #
    cxr
    @72
    clt
    cxr
    clt
    wor
    @75
    xrltso
    a1i
    supexd
    @74
    eqid
    fnmptd
    @62
    @70
    @66
    @74
    @37
    @66
    @74
    wceq
    wph
    vk
    @7
    vx
    @13
    cE
    cfv
    #
    vm
    @48
    @3
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cmpt
    @74
    cZ
    cH
    @13
    @7
    wceq
    #
    vx
    @76
    @79
    @70
    @73
    @13
    @7
    cE
    fveq2
    @80
    cxr
    @78
    @72
    clt
    @80
    @77
    @71
    @80
    vm
    @48
    @8
    @3
    @13
    @7
    cuz
    fveq2
    #
    mpteq1d
    rneqd
    supeq1d
    #
    mpteq12dv
    smflimsuplem7.h
    vx
    @70
    @73
    @7
    cE
    fvex
    mptex
    fvmpt
    adantl
    fneq1d
    mpbird
    fndmd
    @62
    @70
    @73
    cr
    wcel
    #
    vx
    @10
    crab
    #
    @10
    @37
    @70
    @84
    wceq
    wph
    @37
    vk
    @7
    @79
    cr
    wcel
    #
    vx
    @49
    crab
    @84
    cZ
    cE
    cvv
    smflimsuplem7.e
    @80
    @85
    @83
    vx
    @49
    @10
    @80
    @50
    @28
    @85
    @83
    @80
    @49
    @10
    @0
    @80
    vm
    @48
    @8
    @9
    @81
    iineq1d
    eleq2d
    @80
    @79
    @73
    cr
    @82
    eleq1d
    anbi12d
    rabbidva2
    @37
    id
    @37
    vm
    @8
    vy
    cv
    #
    @2
    cfv
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    csup
    #
    cr
    wcel
    #
    vy
    @10
    @84
    cvv
    @83
    @91
    vx
    vy
    @10
    @0
    @86
    wceq
    #
    @73
    @90
    cr
    @92
    cxr
    @72
    @89
    clt
    @92
    @71
    @88
    @92
    vm
    @8
    @3
    @87
    @0
    @86
    @2
    fveq2
    mpteq2dv
    rneqd
    supeq1d
    eleq1d
    cbvrabv
    @37
    vm
    @8
    @9
    cvv
    @37
    @65
    @8
    c0
    wne
    @69
    @8
    @7
    ne0i
    syl
    @9
    cvv
    wcel
    #
    vm
    @8
    wral
    @37
    @93
    vm
    @8
    @2
    @1
    cF
    fvex
    dmex
    rgenw
    a1i
    iinexd
    rabexd
    fvmptd3
    adantl
    @84
    @10
    wss
    @62
    @83
    vx
    @10
    ssrab2
    a1i
    eqsstrd
    eqsstrd
    @63
    @68
    vk
    @7
    @8
    @80
    @19
    @67
    @10
    @80
    @14
    @66
    @13
    @7
    cH
    fveq2
    dmeqd
    sseq1d
    rspcev
    syl2anc
    vk
    @8
    @19
    @10
    iinss
    syl
    ralrimiva
    vn
    cZ
    @20
    @10
    ss2iun
    syl
    sstrd
    wph
    @6
    vx
    @22
    wph
    @24
    wa
    #
    @36
    @6
    @24
    @36
    wph
    @24
    @27
    @36
    @24
    @27
    @18
    @58
    simplbi
    @27
    @36
    @52
    biimpi
    syl
    adantl
    @94
    @35
    @6
    vn
    cZ
    wph
    @24
    vn
    @53
    vn
    @0
    @22
    @54
    @18
    vn
    vx
    @21
    @56
    vn
    cZ
    @20
    nfiu1
    nfrab
    nfel
    nfan
    @55
    @24
    wph
    @18
    @37
    @35
    @6
    wi
    wi
    @24
    @27
    @18
    @58
    simprbi
    wph
    @18
    wa
    #
    @37
    @35
    @6
    @95
    @37
    @35
    w3a
    vx
    cS
    vm
    vk
    cE
    cF
    cH
    cM
    @7
    cZ
    @95
    @37
    @35
    vk
    wph
    @18
    vk
    wph
    vk
    nfv
    vk
    @16
    @17
    vk
    cZ
    @15
    nfmpt1
    vk
    @17
    nfcv
    nfel
    nfan
    @37
    vk
    nfv
    vk
    @0
    @20
    vk
    @0
    nfcv
    vk
    @8
    @19
    nfii1
    nfel
    nf3an
    wph
    @37
    @35
    @44
    @18
    wph
    @37
    @44
    @35
    wph
    @44
    @37
    smflimsuplem7.m
    adantr
    3adant3
    3adant1r
    smflimsuplem7.z
    wph
    @37
    @35
    @46
    @18
    wph
    @37
    @46
    @35
    wph
    @46
    @37
    smflimsuplem7.s
    adantr
    3adant3
    3adant1r
    wph
    @37
    @35
    @47
    @18
    wph
    @37
    @47
    @35
    wph
    @47
    @37
    smflimsuplem7.f
    adantr
    3adant3
    3adant1r
    smflimsuplem7.e
    smflimsuplem7.h
    @95
    @37
    @35
    simp2
    @95
    @37
    @35
    simp3
    wph
    @18
    @37
    @35
    simp1r
    smflimsuplem4
    3exp
    sylan2
    rexlimd
    mpd
    ralrimiva
    jca
    @6
    vx
    @11
    @22
    @18
    vx
    @21
    nfrab1
    #
    vx
    @11
    nfcv
    ssrabf
    sylibr
    sseld
    impbid
    alrimiv
    vx
    @12
    @22
    @6
    vx
    @11
    nfrab1
    @96
    dfcleqf
    sylibr
    eqtrd
end
