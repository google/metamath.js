include "cn0.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cc.mm"
include "c1.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cneg.mm"
include "ccxp.mm"
include "cmpt.mm"
include "cdv.mm"
include "cmin.mm"
include "cmul.mm"
include "cabs.mm"
include "ccnv.mm"
include "cc0.mm"
include "cico.mm"
include "cima.mm"
include "nfcv.mm"
include "cfv.mm"
include "cseq.mm"
include "cli.mm"
include "cdm.mm"
include "cr.mm"
include "crab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cexp.mm"
include "nfmpt1.mm"
include "nfcxfr.mm"
include "nffv.mm"
include "nfseq.mm"
include "nfel1.mm"
include "nfrab.mm"
include "nfsup.mm"
include "nfov.mm"
include "nfima.mm"
include "wceq.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cbvmptf.mm"
include "oveq2i.mm"
include "cvv.mm"
include "cmnf.mm"
include "cioc.mm"
include "cdif.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "crp.mm"
include "wi.mm"
include "1cnd.mm"
include "wss.mm"
include "cnvimass.mm"
include "eqsstri.mm"
include "absf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "sselda.mm"
include "addcld.mm"
include "simpr.mm"
include "wbr.mm"
include "adantr.mm"
include "pncan2d.mm"
include "1red.mm"
include "resubcld.mm"
include "eqeltrrd.mm"
include "1pneg1e0.mm"
include "renegcld.mm"
include "cle.mm"
include "w3a.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "simprbi.mm"
include "eleq2s.mm"
include "0re.mm"
include "ssrab2.mm"
include "ressxr.mm"
include "sstri.mm"
include "supxrcl.mm"
include "ax-mp.mm"
include "eqeltri.mm"
include "elico2.mm"
include "mp2an.mm"
include "sylib.mm"
include "simp3d.mm"
include "adantl.mm"
include "binomcxplemradcnv.mm"
include "breqtrd.mm"
include "absltd.mm"
include "mpbid.mm"
include "simpld.mm"
include "ltadd2dd.mm"
include "syl5eqbrr.mm"
include "syldan.mm"
include "elrpd.mm"
include "ex.mm"
include "eqid.mm"
include "ellogdm.mm"
include "sylanbrc.mm"
include "eldifi.mm"
include "negcld.mm"
include "cxpcld.mm"
include "ovexd.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "c0ex.mm"
include "dvmptc.mm"
include "dvmptid.mm"
include "dvmptadd.mm"
include "0p1e1.mm"
include "mpteq2i.mm"
include "syl6eq.mm"
include "crest.mm"
include "fvex.mm"
include "ctps.mm"
include "cuni.mm"
include "cnfldtps.mm"
include "cnfldbas.mm"
include "tpsuni.mm"
include "restid.mm"
include "eqcomi.mm"
include "cnt.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "ccom.mm"
include "cbl.mm"
include "cnbl0.mm"
include "eqtri.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "0cn.mm"
include "cnfldtopn.mm"
include "blopn.mm"
include "mp3an.mm"
include "isopn3i.mm"
include "dvmptres2.mm"
include "cbvmptv.mm"
include "eqidd.mm"
include "3eqtr3g.mm"
include "dvcncxp1.mm"
include "syl.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "dvmptco.mm"
include "subcld.mm"
include "mulcld.mm"
include "mulid1d.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem binomcxplemdvbinom
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cF: class F
  let vr: setvar r
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  assume binomcxp.a: |- ( ph -> A e. RR+ )
  assume binomcxp.b: |- ( ph -> B e. RR )
  assume binomcxp.lt: |- ( ph -> ( abs ` B ) < ( abs ` A ) )
  assume binomcxp.c: |- ( ph -> C e. CC )
  assume binomcxplem.f: |- F = ( j e. NN0 |-> ( C _Cc j ) )
  assume binomcxplem.s: |- S = ( b e. CC |-> ( k e. NN0 |-> ( ( F ` k ) x. ( b ^ k ) ) ) )
  assume binomcxplem.r: |- R = sup ( { r e. RR | seq 0 ( + , ( S ` r ) ) e. dom ~~> } , RR* , < )
  assume binomcxplem.e: |- E = ( b e. CC |-> ( k e. NN |-> ( ( k x. ( F ` k ) ) x. ( b ^ ( k - 1 ) ) ) ) )
  assume binomcxplem.d: |- D = ( `' abs " ( 0 [,) R ) )

  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint b k
  disjoint C b
  disjoint C k
  disjoint C j
  disjoint F b
  disjoint F k
  disjoint S r
  disjoint b r
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint b y
  assert |- ( ( ph /\ -. C e. NN0 ) -> ( CC _D ( b e. D |-> ( ( 1 + b ) ^c -u C ) ) ) = ( b e. D |-> ( -u C x. ( ( 1 + b ) ^c ( -u C - 1 ) ) ) ) )

  proof
    wph
    cC
    cn0
    wcel
    wn
    #
    wa
    #
    cc
    vb
    cD
    c1
    vb
    cv
    #
    caddc
    co
    #
    cC
    cneg
    #
    ccxp
    co
    #
    cmpt
    #
    cdv
    co
    cc
    vy
    cD
    c1
    vy
    cv
    #
    caddc
    co
    #
    @4
    ccxp
    co
    #
    cmpt
    #
    cdv
    co
    #
    vb
    cD
    @4
    @3
    @4
    c1
    cmin
    co
    #
    ccxp
    co
    #
    cmul
    co
    #
    cmpt
    #
    @6
    @10
    cc
    cdv
    vb
    vy
    cD
    @5
    @9
    vb
    cD
    cabs
    ccnv
    #
    cc0
    cR
    cico
    co
    #
    cima
    #
    binomcxplem.d
    vb
    @16
    @17
    vb
    @16
    nfcv
    vb
    cc0
    cR
    cico
    vb
    cc0
    nfcv
    #
    vb
    cico
    nfcv
    vb
    cR
    caddc
    vr
    cv
    #
    cS
    cfv
    #
    cc0
    cseq
    #
    cli
    cdm
    #
    wcel
    #
    vr
    cr
    crab
    #
    cxr
    clt
    csup
    #
    binomcxplem.r
    vb
    @25
    cxr
    clt
    @24
    vb
    vr
    cr
    vb
    @22
    @23
    vb
    caddc
    @21
    cc0
    @19
    vb
    caddc
    nfcv
    vb
    @20
    cS
    vb
    cS
    vb
    cc
    vk
    cn0
    vk
    cv
    #
    cF
    cfv
    @2
    @27
    cexp
    co
    cmul
    co
    cmpt
    #
    cmpt
    binomcxplem.s
    vb
    cc
    @28
    nfmpt1
    nfcxfr
    vb
    @20
    nfcv
    nffv
    nfseq
    nfel1
    vb
    cr
    nfcv
    nfrab
    vb
    cxr
    nfcv
    vb
    clt
    nfcv
    nfsup
    nfcxfr
    nfov
    nfima
    nfcxfr
    #
    vy
    cD
    nfcv
    #
    vy
    @5
    nfcv
    vb
    @9
    nfcv
    @2
    @7
    wceq
    @3
    @8
    @4
    ccxp
    @2
    @7
    c1
    caddc
    oveq2
    oveq1d
    cbvmptf
    oveq2i
    @1
    @11
    vy
    cD
    @4
    @8
    @12
    ccxp
    co
    #
    cmul
    co
    #
    c1
    cmul
    co
    #
    cmpt
    vy
    cD
    @32
    cmpt
    #
    @15
    @1
    vy
    vx
    @8
    c1
    vx
    cv
    #
    @4
    ccxp
    co
    #
    @4
    @35
    @12
    ccxp
    co
    #
    cmul
    co
    #
    cc
    cc
    @9
    @32
    cc
    cvv
    cD
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    #
    cc
    cr
    cc
    cpr
    wcel
    @1
    cnelprrecn
    a1i
    #
    @41
    @1
    @7
    cD
    wcel
    #
    wa
    #
    @8
    cc
    wcel
    @8
    cr
    wcel
    #
    @8
    crp
    wcel
    #
    wi
    @8
    @40
    wcel
    @43
    c1
    @7
    @43
    1cnd
    #
    @1
    cD
    cc
    @7
    cD
    cc
    wss
    @1
    cD
    cabs
    cdm
    #
    cc
    cD
    @18
    @47
    binomcxplem.d
    cabs
    @17
    cnvimass
    eqsstri
    cc
    cr
    cabs
    absf
    fdmi
    sseqtri
    a1i
    #
    sselda
    #
    addcld
    #
    @43
    @44
    @45
    @43
    @44
    wa
    #
    @8
    @43
    @44
    simpr
    #
    @43
    @44
    @7
    cr
    wcel
    #
    cc0
    @8
    clt
    wbr
    @51
    @8
    c1
    cmin
    co
    @7
    cr
    @51
    c1
    @7
    @51
    1cnd
    @43
    @7
    cc
    wcel
    #
    @44
    @49
    adantr
    pncan2d
    @51
    @8
    c1
    @52
    @51
    1red
    resubcld
    eqeltrrd
    @43
    @53
    wa
    #
    cc0
    c1
    c1
    cneg
    #
    caddc
    co
    @8
    clt
    1pneg1e0
    @55
    @56
    @7
    c1
    @55
    c1
    @55
    1red
    #
    renegcld
    @43
    @53
    simpr
    #
    @57
    @55
    @56
    @7
    clt
    wbr
    #
    @7
    c1
    clt
    wbr
    #
    @55
    @7
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    @59
    @60
    wa
    @43
    @62
    @53
    @43
    @61
    cR
    c1
    clt
    @42
    @61
    cR
    clt
    wbr
    #
    @1
    @42
    @61
    cr
    wcel
    #
    cc0
    @61
    cle
    wbr
    #
    @63
    @42
    @61
    @17
    wcel
    #
    @64
    @65
    @63
    w3a
    #
    @66
    @7
    @18
    cD
    @7
    @18
    wcel
    #
    @54
    @66
    cc
    cr
    cabs
    wf
    cabs
    cc
    wfn
    @68
    @54
    @66
    wa
    wb
    absf
    cc
    cr
    cabs
    ffn
    cc
    @7
    @17
    cabs
    elpreima
    mp2b
    simprbi
    binomcxplem.d
    eleq2s
    cc0
    cr
    wcel
    cR
    cxr
    wcel
    #
    @66
    @67
    wb
    0re
    cR
    @26
    cxr
    binomcxplem.r
    @25
    cxr
    wss
    @26
    cxr
    wcel
    @25
    cr
    cxr
    @24
    vr
    cr
    ssrab2
    ressxr
    sstri
    @25
    supxrcl
    ax-mp
    eqeltri
    #
    cc0
    cR
    @61
    elico2
    mp2an
    sylib
    simp3d
    adantl
    @1
    cR
    c1
    wceq
    @42
    wph
    cA
    cB
    cC
    cR
    cS
    vj
    vk
    cF
    vr
    vb
    binomcxp.a
    binomcxp.b
    binomcxp.lt
    binomcxp.c
    binomcxplem.f
    binomcxplem.s
    binomcxplem.r
    binomcxplemradcnv
    adantr
    breqtrd
    adantr
    @55
    @7
    c1
    @58
    @57
    absltd
    mpbid
    simpld
    ltadd2dd
    syl5eqbrr
    syldan
    elrpd
    ex
    @8
    @40
    @40
    eqid
    #
    ellogdm
    sylanbrc
    @46
    @1
    @35
    @40
    wcel
    #
    wa
    #
    @35
    @4
    @72
    @35
    cc
    wcel
    #
    @1
    @35
    cc
    @39
    eldifi
    adantl
    @1
    @4
    cc
    wcel
    #
    @72
    @1
    cC
    wph
    cC
    cc
    wcel
    #
    @0
    binomcxp.c
    adantr
    #
    negcld
    #
    adantr
    cxpcld
    @73
    @4
    @37
    cmul
    ovexd
    @1
    cc
    vx
    cD
    c1
    @35
    caddc
    co
    #
    cmpt
    #
    cdv
    co
    vx
    cD
    c1
    cmpt
    cc
    vy
    cD
    @8
    cmpt
    #
    cdv
    co
    vy
    cD
    c1
    cmpt
    @1
    vx
    @79
    c1
    cc
    ccnfld
    ctopn
    cfv
    #
    @82
    cc
    cc
    cD
    cD
    @41
    @1
    @74
    wa
    #
    c1
    @35
    @83
    1cnd
    #
    @1
    @74
    simpr
    #
    addcld
    @84
    @1
    cc
    vx
    cc
    @79
    cmpt
    cdv
    co
    vx
    cc
    cc0
    c1
    caddc
    co
    #
    cmpt
    vx
    cc
    c1
    cmpt
    @1
    vx
    c1
    cc0
    @35
    c1
    cc
    cvv
    cc
    cc
    @41
    @84
    cc0
    cvv
    wcel
    @83
    c0ex
    a1i
    @1
    vx
    c1
    cc
    @41
    @1
    1cnd
    dvmptc
    @85
    @84
    @1
    vx
    cc
    @41
    dvmptid
    dvmptadd
    vx
    cc
    @86
    c1
    0p1e1
    mpteq2i
    syl6eq
    @48
    @82
    cc
    crest
    co
    #
    @82
    @82
    cvv
    wcel
    @87
    @82
    wceq
    ccnfld
    ctopn
    fvex
    @82
    cvv
    cc
    ccnfld
    ctps
    wcel
    cc
    @82
    cuni
    wceq
    cnfldtps
    cc
    @82
    ccnfld
    cnfldbas
    @82
    eqid
    #
    tpsuni
    ax-mp
    restid
    ax-mp
    eqcomi
    @88
    cD
    @82
    cnt
    cfv
    cfv
    cD
    wceq
    #
    @1
    @82
    ctop
    wcel
    cD
    @82
    wcel
    @89
    @82
    @88
    cnfldtop
    cD
    cc0
    cR
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    @82
    cD
    @18
    @91
    binomcxplem.d
    @69
    @18
    @91
    wceq
    @70
    @90
    cR
    @90
    eqid
    cnbl0
    ax-mp
    eqtri
    @90
    cc
    cxmt
    cfv
    wcel
    cc0
    cc
    wcel
    @69
    @91
    @82
    wcel
    cnxmet
    0cn
    @70
    @90
    cc0
    cR
    @82
    cc
    @82
    @88
    cnfldtopn
    blopn
    mp3an
    eqeltri
    cD
    @82
    isopn3i
    mp2an
    a1i
    dvmptres2
    @80
    @81
    cc
    cdv
    vx
    vy
    cD
    @79
    @8
    @35
    @7
    c1
    caddc
    oveq2
    cbvmptv
    oveq2i
    vx
    vy
    cD
    c1
    c1
    @35
    @7
    wceq
    c1
    eqidd
    cbvmptv
    3eqtr3g
    @1
    @75
    cc
    vx
    @40
    @36
    cmpt
    cdv
    co
    vx
    @40
    @38
    cmpt
    wceq
    @78
    vx
    @4
    @40
    @71
    dvcncxp1
    syl
    @35
    @8
    @4
    ccxp
    oveq1
    @35
    @8
    wceq
    @37
    @31
    @4
    cmul
    @35
    @8
    @12
    ccxp
    oveq1
    oveq2d
    dvmptco
    @1
    vy
    cD
    @33
    @32
    @43
    @32
    @43
    @4
    @31
    @43
    cC
    @1
    @76
    @42
    @77
    adantr
    negcld
    #
    @43
    @8
    @12
    @50
    @43
    @4
    c1
    @92
    @46
    subcld
    cxpcld
    mulcld
    mulid1d
    mpteq2dva
    @34
    @15
    wceq
    @1
    vy
    vb
    cD
    @32
    @14
    @30
    @29
    vb
    @32
    nfcv
    vy
    @14
    nfcv
    @7
    @2
    wceq
    #
    @31
    @13
    @4
    cmul
    @93
    @8
    @3
    @12
    ccxp
    @7
    @2
    c1
    caddc
    oveq2
    oveq1d
    oveq2d
    cbvmptf
    a1i
    3eqtrd
    syl5eq
end
