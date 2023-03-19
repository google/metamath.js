include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cpnf.mm"
include "wceq.mm"
include "wrex.mm"
include "ciun.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfmpt.mm"
include "nffv.mm"
include "nfmpt1.mm"
include "nfeq.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "cxr.mm"
include "cvv.mm"
include "wral.mm"
include "ralrimiva.mm"
include "iunexg.mm"
include "syl2anc.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "wa.mm"
include "eliun.mm"
include "biimpi.mm"
include "adantl.mm"
include "nfel.mm"
include "nfan.mm"
include "nfel1.mm"
include "wi.mm"
include "3exp.mm"
include "adantr.mm"
include "rexlimd.mm"
include "mpd.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0xrcl.mm"
include "3ad2ant1.mm"
include "cle.mm"
include "id.mm"
include "eqcomd.mm"
include "3adant1.mm"
include "wbr.mm"
include "adantlr.mm"
include "wss.mm"
include "ssiun2.mm"
include "sge0lessmpt.mm"
include "3adant3.mm"
include "eqbrtrd.mm"
include "xrgepnfd.mm"
include "wf.mm"
include "csb.mm"
include "nfcsb1v.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "nff.mm"
include "mpteq1d.mm"
include "feq12d.mm"
include "imp31.mm"
include "sge0cl.mm"
include "fveq2d.mm"
include "cbvmpt.mm"
include "crn.mm"
include "fvexd.mm"
include "elrnmpt1.mm"
include "eqeltrd.mm"
include "sge0pnfval.mm"
include "eqtr4d.mm"
include "imp.mm"
include "wn.mm"
include "wne.mm"
include "simpl.mm"
include "ralnex.mm"
include "df-ne.mm"
include "bicomi.mm"
include "ralbii.mm"
include "sylbb1.mm"
include "eleq1d.mm"
include "wdisj.mm"
include "cbvdisj.mm"
include "sylib.mm"
include "3anbi3d.mm"
include "nf3an.mm"
include "eleq2d.mm"
include "3anbi23d.mm"
include "imbi1d.mm"
include "3adant1r.mm"
include "cr.mm"
include "simpr.mm"
include "nfne.mm"
include "a1i.mm"
include "eqtrd.mm"
include "neeq1d.mm"
include "rspc.mm"
include "sylc.mm"
include "neneqd.mm"
include "adantll.mm"
include "3expa.mm"
include "sge0repnf.mm"
include "mpbird.mm"
include "cbviun.mm"
include "mpteq1i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "syl5eqelr.mm"
include "exp31.mm"
include "sge0iunmptlemre.mm"
include "3eqtr4d.mm"
include "pm2.61dan.mm"

theorem sge0iunmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let cW: class W
  let vj: setvar j
  let vy: setvar y
  assume sge0iunmpt.a: |- ( ph -> A e. V )
  assume sge0iunmpt.b: |- ( ( ph /\ x e. A ) -> B e. W )
  assume sge0iunmpt.dj: |- ( ph -> Disj_ x e. A B )
  assume sge0iunmpt.c: |- ( ( ph /\ x e. A /\ k e. B ) -> C e. ( 0 [,] +oo ) )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B k
  disjoint C x
  disjoint W x
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A j
  disjoint A y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint k y
  disjoint x y
  disjoint B j
  disjoint B y
  disjoint C j
  disjoint C y
  disjoint W y
  disjoint j ph
  disjoint ph y
  assert |- ( ph -> ( sum^ ` ( k e. U_ x e. A B |-> C ) ) = ( sum^ ` ( x e. A |-> ( sum^ ` ( k e. B |-> C ) ) ) ) )

  proof
    wph
    vk
    cB
    cC
    cmpt
    #
    csumge0
    cfv
    #
    cpnf
    wceq
    #
    vx
    cA
    wrex
    #
    vk
    vx
    cA
    cB
    ciun
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    vx
    cA
    @1
    cmpt
    #
    csumge0
    cfv
    #
    wceq
    #
    wph
    @3
    @9
    wph
    @2
    @9
    vx
    cA
    wph
    vx
    nfv
    #
    vx
    @6
    @8
    vx
    @5
    csumge0
    vx
    csumge0
    nfcv
    #
    vx
    vk
    @4
    cC
    vx
    cA
    cB
    nfiu1
    #
    vx
    cC
    nfcv
    #
    nfmpt
    nffv
    vx
    @7
    csumge0
    @11
    vx
    cA
    @1
    nfmpt1
    nffv
    nfeq
    wph
    vx
    cv
    #
    cA
    wcel
    #
    @2
    @9
    wph
    @15
    @2
    w3a
    #
    @6
    cpnf
    @8
    @16
    @6
    wph
    @15
    @6
    cxr
    wcel
    @2
    wph
    @5
    cvv
    @4
    wph
    cA
    cV
    wcel
    #
    cB
    cW
    wcel
    #
    vx
    cA
    wral
    @4
    cvv
    wcel
    #
    sge0iunmpt.a
    wph
    @18
    vx
    cA
    sge0iunmpt.b
    ralrimiva
    vx
    cA
    cB
    cV
    cW
    iunexg
    syl2anc
    #
    wph
    vk
    @4
    cC
    cc0
    cpnf
    cicc
    co
    #
    @5
    wph
    vk
    cv
    #
    @4
    wcel
    #
    wa
    #
    @22
    cB
    wcel
    #
    vx
    cA
    wrex
    #
    cC
    @21
    wcel
    #
    @23
    @26
    wph
    @23
    @26
    vx
    @22
    cA
    cB
    eliun
    biimpi
    adantl
    @24
    @25
    @27
    vx
    cA
    wph
    @23
    vx
    @10
    vx
    @22
    @4
    vx
    @22
    nfcv
    #
    @12
    nfel
    nfan
    vx
    cC
    @21
    @13
    nfel1
    #
    wph
    @15
    @25
    @27
    wi
    wi
    @23
    wph
    @15
    @25
    @27
    sge0iunmpt.c
    3exp
    #
    adantr
    rexlimd
    mpd
    #
    @5
    eqid
    fmptd
    sge0xrcl
    #
    3ad2ant1
    @16
    cpnf
    @1
    @6
    cle
    @15
    @2
    cpnf
    @1
    wceq
    #
    wph
    @2
    @33
    @15
    @2
    @1
    cpnf
    @2
    id
    eqcomd
    adantl
    #
    3adant1
    wph
    @15
    @1
    @6
    cle
    wbr
    @2
    wph
    @15
    wa
    #
    vk
    @4
    cC
    cB
    cvv
    wph
    @19
    @15
    @20
    adantr
    wph
    @23
    @27
    @15
    @31
    adantlr
    @15
    cB
    @4
    wss
    wph
    vx
    cA
    cB
    ssiun2
    adantl
    sge0lessmpt
    3adant3
    eqbrtrd
    xrgepnfd
    @16
    @7
    cV
    cA
    wph
    @15
    @17
    @2
    sge0iunmpt.a
    3ad2ant1
    wph
    @15
    cA
    @21
    @7
    wf
    @2
    @35
    vy
    cA
    vk
    vx
    vy
    cv
    #
    cB
    csb
    #
    cC
    cmpt
    #
    csumge0
    cfv
    #
    @21
    @7
    @35
    @36
    cA
    wcel
    #
    wa
    @38
    vx
    @36
    cW
    csb
    #
    @37
    wph
    @40
    @37
    @41
    wcel
    #
    @15
    @35
    @18
    wi
    #
    wph
    @40
    wa
    #
    @42
    wi
    vx
    vy
    @44
    @42
    vx
    @44
    vx
    nfv
    #
    vx
    @37
    @41
    vx
    @36
    cB
    nfcsb1v
    #
    vx
    @36
    cW
    nfcsb1v
    nfel
    nfim
    @14
    @36
    wceq
    #
    @35
    @44
    @18
    @42
    @47
    @15
    @40
    wph
    @14
    @36
    cA
    eleq1
    #
    anbi2d
    #
    @47
    cB
    @37
    cW
    @41
    vx
    @36
    cB
    csbeq1a
    #
    vx
    @36
    cW
    csbeq1a
    eleq12d
    imbi12d
    sge0iunmpt.b
    chvar
    adantlr
    wph
    @40
    @37
    @21
    @38
    wf
    #
    @15
    @35
    cB
    @21
    @0
    wf
    #
    wi
    @44
    @51
    wi
    vx
    vy
    @44
    @51
    vx
    @45
    vx
    @37
    @21
    @38
    vx
    vk
    @37
    cC
    @46
    @13
    nfmpt
    #
    @46
    vx
    @21
    nfcv
    nff
    nfim
    @47
    @35
    @44
    @52
    @51
    @49
    @47
    cB
    @37
    @21
    @0
    @38
    @47
    vk
    cB
    @37
    cC
    @50
    mpteq1d
    #
    @50
    feq12d
    imbi12d
    @35
    vk
    cB
    cC
    @21
    @0
    wph
    @15
    @25
    @27
    @30
    imp31
    @0
    eqid
    fmptd
    #
    chvar
    adantlr
    sge0cl
    vx
    vy
    cA
    @1
    @39
    vy
    @1
    nfcv
    #
    vx
    @38
    csumge0
    @11
    @53
    nffv
    @47
    @0
    @38
    csumge0
    @54
    fveq2d
    cbvmpt
    fmptd
    3adant3
    @15
    @2
    cpnf
    @7
    crn
    #
    wcel
    wph
    @15
    @2
    wa
    cpnf
    @1
    @57
    @34
    @15
    @1
    @57
    wcel
    #
    @2
    @15
    @15
    @1
    cvv
    wcel
    @58
    @15
    id
    @15
    @0
    csumge0
    fvexd
    vx
    cA
    @1
    @7
    cvv
    @7
    eqid
    #
    elrnmpt1
    syl2anc
    adantr
    eqeltrd
    3adant1
    sge0pnfval
    eqtr4d
    3exp
    rexlimd
    imp
    wph
    @3
    wn
    #
    wa
    wph
    @1
    cpnf
    wne
    #
    vx
    cA
    wral
    #
    @9
    wph
    @60
    simpl
    @60
    @62
    wph
    @2
    wn
    #
    vx
    cA
    wral
    @60
    @62
    @2
    vx
    cA
    ralnex
    @63
    @61
    vx
    cA
    @61
    @63
    @1
    cpnf
    df-ne
    bicomi
    ralbii
    sylbb1
    adantl
    wph
    @62
    wa
    #
    vj
    vy
    cA
    @37
    ciun
    #
    vk
    vj
    cv
    #
    cC
    csb
    #
    cmpt
    #
    csumge0
    cfv
    #
    vy
    cA
    vj
    @37
    @67
    cmpt
    #
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @6
    @8
    @64
    vy
    cA
    @37
    @67
    vj
    cV
    cW
    wph
    @17
    @62
    sge0iunmpt.a
    adantr
    wph
    @40
    @37
    cW
    wcel
    #
    @62
    @43
    @44
    @74
    wi
    vx
    vy
    @44
    @74
    vx
    @45
    vx
    @37
    cW
    @46
    vx
    cW
    nfcv
    nfel
    nfim
    @47
    @35
    @44
    @18
    @74
    @49
    @47
    cB
    @37
    cW
    @50
    eleq1d
    imbi12d
    sge0iunmpt.b
    chvar
    adantlr
    #
    wph
    vy
    cA
    @37
    wdisj
    #
    @62
    wph
    vx
    cA
    cB
    wdisj
    @76
    sge0iunmpt.dj
    vx
    vy
    cA
    cB
    @37
    vy
    cB
    nfcv
    #
    @46
    @50
    cbvdisj
    sylib
    adantr
    wph
    @40
    @66
    @37
    wcel
    #
    @67
    @21
    wcel
    #
    @62
    wph
    @40
    @22
    @37
    wcel
    #
    w3a
    #
    @27
    wi
    #
    wph
    @40
    @78
    w3a
    #
    @79
    wi
    vk
    vj
    @83
    @79
    vk
    @83
    vk
    nfv
    vk
    @67
    @21
    vk
    @66
    cC
    nfcsb1v
    #
    nfel1
    nfim
    @22
    @66
    wceq
    #
    @81
    @83
    @27
    @79
    @85
    @80
    @78
    wph
    @40
    @22
    @66
    @37
    eleq1
    3anbi3d
    @85
    cC
    @67
    @21
    vk
    @66
    cC
    csbeq1a
    #
    eleq1d
    imbi12d
    wph
    @15
    @25
    w3a
    #
    @27
    wi
    @82
    vx
    vy
    @81
    @27
    vx
    wph
    @40
    @80
    vx
    @10
    @40
    vx
    nfv
    vx
    @22
    @37
    @28
    @46
    nfel
    nf3an
    @29
    nfim
    @47
    @87
    @81
    @27
    @47
    @15
    @40
    @25
    @80
    wph
    @48
    @47
    cB
    @37
    @22
    @50
    eleq2d
    3anbi23d
    imbi1d
    sge0iunmpt.c
    chvar
    chvar
    #
    3adant1r
    @64
    @40
    wa
    #
    @71
    cr
    wcel
    @71
    cpnf
    wceq
    wn
    #
    @62
    @40
    @90
    wph
    @62
    @40
    wa
    #
    @71
    cpnf
    @91
    @40
    @62
    @71
    cpnf
    wne
    #
    @62
    @40
    simpr
    @62
    @40
    simpl
    @40
    @62
    wa
    @40
    @62
    @92
    @40
    @62
    simpl
    @40
    @62
    simpr
    @61
    @92
    vx
    @36
    cA
    vx
    @71
    cpnf
    vx
    @70
    csumge0
    @11
    vx
    vj
    @37
    @67
    @46
    vx
    @67
    nfcv
    nfmpt
    nffv
    #
    vx
    cpnf
    nfcv
    nfne
    @47
    @1
    @71
    cpnf
    @47
    @0
    @70
    csumge0
    @47
    @0
    @38
    @70
    @54
    @38
    @70
    wceq
    @47
    vk
    vj
    @37
    cC
    @67
    vj
    cC
    nfcv
    #
    @84
    @86
    cbvmpt
    a1i
    eqtrd
    fveq2d
    #
    neeq1d
    rspc
    sylc
    syl2anc
    neneqd
    adantll
    @89
    @70
    cW
    @37
    @75
    wph
    @40
    @37
    @21
    @70
    wf
    @62
    @44
    vj
    @37
    @67
    @21
    @70
    wph
    @40
    @78
    @79
    @88
    3expa
    #
    @70
    eqid
    fmptd
    adantlr
    sge0repnf
    mpbird
    wph
    @69
    cxr
    wcel
    @62
    wph
    @69
    @6
    cxr
    @5
    @68
    csumge0
    @5
    vj
    @4
    @67
    cmpt
    @68
    vk
    vj
    @4
    cC
    @67
    @94
    @84
    @86
    cbvmpt
    vj
    @4
    @65
    @67
    vx
    vy
    cA
    cB
    @37
    @77
    @46
    @50
    cbviun
    #
    mpteq1i
    eqtri
    fveq2i
    #
    @32
    syl5eqelr
    adantr
    wph
    @73
    cxr
    wcel
    @62
    wph
    @73
    @8
    cxr
    @7
    @72
    csumge0
    vx
    vy
    cA
    @1
    @71
    @56
    @93
    @95
    cbvmpt
    fveq2i
    #
    wph
    @7
    cV
    cA
    sge0iunmpt.a
    wph
    vx
    cA
    @1
    @21
    @7
    @35
    @0
    cW
    cB
    sge0iunmpt.b
    @55
    sge0cl
    @59
    fmptd
    sge0xrcl
    syl5eqelr
    adantr
    wph
    @65
    @21
    @68
    wf
    @62
    wph
    vj
    @65
    @67
    @21
    @68
    wph
    @66
    @65
    wcel
    #
    wa
    #
    @78
    vy
    cA
    wrex
    #
    @79
    @100
    @102
    wph
    @100
    @102
    vy
    @66
    cA
    @37
    eliun
    biimpi
    adantl
    @101
    @78
    @79
    vy
    cA
    wph
    @100
    vy
    wph
    vy
    nfv
    vy
    @66
    @65
    vy
    @66
    nfcv
    vy
    cA
    @37
    nfiu1
    nfel
    nfan
    @79
    vy
    nfv
    wph
    @40
    @78
    @79
    wi
    wi
    @100
    wph
    @40
    @78
    @79
    @96
    exp31
    adantr
    rexlimd
    mpd
    @68
    eqid
    fmptd
    adantr
    wph
    @65
    cvv
    wcel
    @62
    wph
    @65
    @4
    cvv
    @97
    @20
    syl5eqelr
    adantr
    sge0iunmptlemre
    @6
    @69
    wceq
    @64
    @98
    a1i
    @8
    @73
    wceq
    @64
    @99
    a1i
    3eqtr4d
    syl2anc
    pm2.61dan
end
