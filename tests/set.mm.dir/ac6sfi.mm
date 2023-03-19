include "cfn.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "cv.mm"
include "wf.mm"
include "wa.mm"
include "wex.mm"
include "wi.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cfv.mm"
include "wsbc.mm"
include "wceq.mm"
include "raleq.mm"
include "feq2.mm"
include "anbi12d.mm"
include "exbidv.mm"
include "imbi12d.mm"
include "weq.mm"
include "feq1.mm"
include "fvex.mm"
include "sbcie.mm"
include "fveq1.mm"
include "sbceq1d.mm"
include "syl5bbr.mm"
include "ralbidv.mm"
include "cbvexv.mm"
include "syl6bb.mm"
include "f0.mm"
include "0ex.mm"
include "ral0.mm"
include "biantru.mm"
include "spcev.mm"
include "mp1i.mm"
include "wel.mm"
include "wn.mm"
include "wss.mm"
include "ssun1.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "imim1i.mm"
include "ssun2.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "ralsnsg.mm"
include "sbcrex.mm"
include "bitri.mm"
include "sylib.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfsbc1v.mm"
include "nfral.mm"
include "nfan.mm"
include "nfex.mm"
include "nfim.mm"
include "w3a.mm"
include "cop.mm"
include "cin.mm"
include "simprl.mm"
include "wf1o.mm"
include "f1osn.mm"
include "f1of.mm"
include "simpl2.mm"
include "snssd.mm"
include "fssd.mm"
include "simpl1.mm"
include "disjsn.mm"
include "sylibr.mm"
include "fun2.mm"
include "syl21anc.mm"
include "simprr.mm"
include "wne.mm"
include "eleq1a.mm"
include "necon3bd.mm"
include "impcom.mm"
include "fvunsn.mm"
include "dfsbcq.mm"
include "syl6rbb.mm"
include "3syl.mm"
include "ralbidva.mm"
include "syl.mm"
include "mpbid.mm"
include "simpl3.mm"
include "wfun.mm"
include "ffun.mm"
include "cdm.mm"
include "vsnid.mm"
include "dmsnop.mm"
include "eleqtrri.mm"
include "funssfv.mm"
include "mp3an23.mm"
include "fvsn.mm"
include "syl6req.mm"
include "elsni.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "biimparc.mm"
include "sbceq1a.mm"
include "ralun.mm"
include "syl2anc.mm"
include "snex.mm"
include "unex.mm"
include "ex.mm"
include "exlimdv.mm"
include "3exp.mm"
include "rexlimd.mm"
include "syl5.mm"
include "a2d.mm"
include "adantl.mm"
include "findcard2s.mm"
include "imp.mm"

theorem ac6sfi
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let vg: setvar g
  assume ac6sfi.1: |- ( y = ( f ` x ) -> ( ph <-> ps ) )

  disjoint f x
  disjoint A f
  disjoint A x
  disjoint f y
  disjoint B f
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint f ph
  disjoint ps y
  disjoint f u
  disjoint f w
  disjoint f z
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint A u
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A z
  disjoint f g
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint u y
  disjoint B u
  disjoint w y
  disjoint B w
  disjoint y z
  disjoint B z
  disjoint g ph
  disjoint ph u
  disjoint ph w
  disjoint ph z
  disjoint g ps
  disjoint ps u
  disjoint ps w
  disjoint ps z
  assert |- ( ( A e. Fin /\ A. x e. A E. y e. B ph ) -> E. f ( f : A --> B /\ A. x e. A ps ) )

  proof
    cA
    cfn
    wcel
    wph
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    cA
    cB
    vf
    cv
    #
    wf
    #
    wps
    vx
    cA
    wral
    #
    wa
    #
    vf
    wex
    #
    @0
    vx
    vu
    cv
    #
    wral
    #
    @7
    cB
    @2
    wf
    #
    wps
    vx
    @7
    wral
    #
    wa
    #
    vf
    wex
    #
    wi
    @0
    vx
    c0
    wral
    #
    c0
    cB
    @2
    wf
    #
    wps
    vx
    c0
    wral
    #
    wa
    #
    vf
    wex
    #
    wi
    @0
    vx
    vw
    cv
    #
    wral
    #
    @18
    cB
    @2
    wf
    #
    wps
    vx
    @18
    wral
    #
    wa
    #
    vf
    wex
    #
    wi
    #
    @0
    vx
    @18
    vz
    cv
    #
    csn
    #
    cun
    #
    wral
    #
    @27
    cB
    vg
    cv
    #
    wf
    #
    wph
    vy
    vx
    cv
    #
    @29
    cfv
    #
    wsbc
    #
    vx
    @27
    wral
    #
    wa
    #
    vg
    wex
    #
    wi
    #
    @1
    @6
    wi
    vu
    vw
    vz
    cA
    @7
    c0
    wceq
    #
    @8
    @13
    @12
    @17
    @0
    vx
    @7
    c0
    raleq
    @38
    @11
    @16
    vf
    @38
    @9
    @14
    @10
    @15
    @7
    c0
    cB
    @2
    feq2
    wps
    vx
    @7
    c0
    raleq
    anbi12d
    exbidv
    imbi12d
    vu
    vw
    weq
    #
    @8
    @19
    @12
    @23
    @0
    vx
    @7
    @18
    raleq
    @39
    @11
    @22
    vf
    @39
    @9
    @20
    @10
    @21
    @7
    @18
    cB
    @2
    feq2
    wps
    vx
    @7
    @18
    raleq
    anbi12d
    exbidv
    imbi12d
    @7
    @27
    wceq
    #
    @8
    @28
    @12
    @36
    @0
    vx
    @7
    @27
    raleq
    @40
    @12
    @27
    cB
    @2
    wf
    #
    wps
    vx
    @27
    wral
    #
    wa
    #
    vf
    wex
    @36
    @40
    @11
    @43
    vf
    @40
    @9
    @41
    @10
    @42
    @7
    @27
    cB
    @2
    feq2
    wps
    vx
    @7
    @27
    raleq
    anbi12d
    exbidv
    @43
    @35
    vf
    vg
    vf
    vg
    weq
    #
    @41
    @30
    @42
    @34
    @27
    cB
    @2
    @29
    feq1
    @44
    wps
    @33
    vx
    @27
    wps
    wph
    vy
    @31
    @2
    cfv
    #
    wsbc
    #
    @44
    @33
    wph
    wps
    vy
    @45
    @31
    @2
    fvex
    ac6sfi.1
    sbcie
    #
    @44
    wph
    vy
    @45
    @32
    @31
    @2
    @29
    fveq1
    sbceq1d
    syl5bbr
    ralbidv
    anbi12d
    cbvexv
    syl6bb
    imbi12d
    @7
    cA
    wceq
    #
    @8
    @1
    @12
    @6
    @0
    vx
    @7
    cA
    raleq
    @48
    @11
    @5
    vf
    @48
    @9
    @3
    @10
    @4
    @7
    cA
    cB
    @2
    feq2
    wps
    vx
    @7
    cA
    raleq
    anbi12d
    exbidv
    imbi12d
    c0
    cB
    c0
    wf
    #
    @17
    @13
    cB
    f0
    @16
    @49
    vf
    c0
    0ex
    @16
    @14
    @2
    c0
    wceq
    @49
    @15
    @14
    wps
    vx
    ral0
    biantru
    c0
    cB
    @2
    c0
    feq1
    syl5bbr
    spcev
    mp1i
    vz
    vw
    wel
    #
    wn
    #
    @24
    @37
    wi
    @18
    cfn
    wcel
    @24
    @28
    @23
    wi
    @51
    @37
    @28
    @19
    @23
    @18
    @27
    wss
    @28
    @19
    wi
    @18
    @26
    ssun1
    @0
    vx
    @18
    @27
    ssralv
    ax-mp
    imim1i
    @51
    @28
    @23
    @36
    @28
    wph
    vx
    @25
    wsbc
    #
    vy
    cB
    wrex
    #
    @51
    @23
    @36
    wi
    #
    @28
    @0
    vx
    @26
    wral
    #
    @53
    @26
    @27
    wss
    @28
    @55
    wi
    @26
    @18
    ssun2
    @0
    vx
    @26
    @27
    ssralv
    ax-mp
    @55
    @0
    vx
    @25
    wsbc
    #
    @53
    @25
    cvv
    wcel
    #
    @55
    @56
    wb
    vz
    vex
    #
    @0
    vx
    @25
    cvv
    ralsnsg
    ax-mp
    wph
    vx
    vy
    @25
    cB
    sbcrex
    bitri
    sylib
    @51
    @52
    @54
    vy
    cB
    @51
    vy
    nfv
    @23
    @36
    vy
    @23
    vy
    nfv
    @35
    vy
    vg
    @30
    @34
    vy
    @30
    vy
    nfv
    @33
    vy
    vx
    @27
    vy
    @27
    nfcv
    wph
    vy
    @32
    nfsbc1v
    nfral
    nfan
    nfex
    nfim
    @51
    vy
    cv
    #
    cB
    wcel
    #
    @52
    @54
    @51
    @60
    @52
    w3a
    #
    @22
    @36
    vf
    @61
    @22
    @36
    @61
    @22
    wa
    #
    @27
    cB
    @2
    @25
    @59
    cop
    #
    csn
    #
    cun
    #
    wf
    #
    wph
    vy
    @31
    @65
    cfv
    #
    wsbc
    #
    vx
    @27
    wral
    #
    @36
    @62
    @20
    @26
    cB
    @64
    wf
    @18
    @26
    cin
    c0
    wceq
    #
    @66
    @61
    @20
    @21
    simprl
    @62
    @26
    @59
    csn
    #
    cB
    @64
    @26
    @71
    @64
    wf1o
    @26
    @71
    @64
    wf
    @62
    @25
    @59
    @58
    vy
    vex
    #
    f1osn
    @26
    @71
    @64
    f1of
    mp1i
    @62
    @59
    cB
    @51
    @60
    @52
    @22
    simpl2
    snssd
    fssd
    @62
    @51
    @70
    @51
    @60
    @52
    @22
    simpl1
    #
    @18
    @25
    disjsn
    sylibr
    @18
    @26
    cB
    @2
    @64
    fun2
    syl21anc
    #
    @62
    @68
    vx
    @18
    wral
    #
    @68
    vx
    @26
    wral
    #
    @69
    @62
    @21
    @75
    @61
    @20
    @21
    simprr
    @62
    @51
    @21
    @75
    wb
    @73
    @51
    wps
    @68
    vx
    @18
    @51
    vx
    vw
    wel
    #
    wa
    @25
    @31
    wne
    #
    @67
    @45
    wceq
    #
    wps
    @68
    wb
    @77
    @51
    @78
    @77
    @50
    @25
    @31
    @31
    @18
    @25
    eleq1a
    necon3bd
    impcom
    @2
    @25
    @59
    @31
    fvunsn
    @79
    @68
    @46
    wps
    wph
    vy
    @67
    @45
    dfsbcq
    @47
    syl6rbb
    3syl
    ralbidva
    syl
    mpbid
    @62
    @52
    @76
    @51
    @60
    @52
    @22
    simpl3
    @62
    @59
    @25
    @65
    cfv
    #
    wceq
    #
    @52
    @76
    wb
    @62
    @80
    @25
    @64
    cfv
    #
    @59
    @62
    @66
    @65
    wfun
    #
    @80
    @82
    wceq
    #
    @74
    @27
    cB
    @65
    ffun
    @83
    @64
    @65
    wss
    @25
    @64
    cdm
    #
    wcel
    @84
    @64
    @2
    ssun2
    @25
    @26
    @85
    vz
    vsnid
    @25
    @59
    @72
    dmsnop
    eleqtrri
    @25
    @65
    @64
    funssfv
    mp3an23
    3syl
    @25
    @59
    @58
    @72
    fvsn
    syl6req
    @52
    wph
    vx
    @26
    wral
    #
    @81
    @76
    @57
    @86
    @52
    wb
    @58
    wph
    vx
    @25
    cvv
    ralsnsg
    ax-mp
    @81
    wph
    @68
    vx
    @26
    @81
    @31
    @26
    wcel
    #
    wa
    @59
    @67
    wceq
    #
    wph
    @68
    wb
    @87
    @88
    @81
    @87
    @67
    @80
    @59
    @87
    @31
    @25
    @65
    @31
    @25
    elsni
    fveq2d
    eqeq2d
    biimparc
    wph
    vy
    @67
    sbceq1a
    syl
    ralbidva
    syl5bbr
    syl
    mpbid
    @68
    vx
    @18
    @26
    ralun
    syl2anc
    @35
    @66
    @69
    wa
    vg
    @65
    @2
    @64
    vf
    vex
    @63
    snex
    unex
    @29
    @65
    wceq
    #
    @30
    @66
    @34
    @69
    @27
    cB
    @29
    @65
    feq1
    @89
    @33
    @68
    vx
    @27
    @89
    wph
    vy
    @32
    @67
    @31
    @29
    @65
    fveq1
    sbceq1d
    ralbidv
    anbi12d
    spcev
    syl2anc
    ex
    exlimdv
    3exp
    rexlimd
    syl5
    a2d
    syl5
    adantl
    findcard2s
    imp
end
