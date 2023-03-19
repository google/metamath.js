include "cv.mm"
include "wpss.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wss.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "w3a.mm"
include "cuni.mm"
include "wi.mm"
include "wal.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wa.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "ssnum.mm"
include "sylancl.mm"
include "lbsextlem1.mm"
include "clss.mm"
include "ciun.mm"
include "clvec.mm"
include "adantr.mm"
include "eqid.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "lbsextlem3.mm"
include "ex.mm"
include "alrimiv.mm"
include "zornn0g.mm"
include "syl3anc.mm"
include "wceq.mm"
include "simprl.mm"
include "weq.mm"
include "sseq2.mm"
include "difeq1.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "notbid.mm"
include "raleqbi1dv.mm"
include "anbi12d.mm"
include "elrab2.mm"
include "sylib.mm"
include "simpld.mm"
include "elpwid.mm"
include "clmod.mm"
include "lveclmod.mm"
include "syl.mm"
include "lspssv.mm"
include "syl2anc.mm"
include "cun.mm"
include "ssun1.mm"
include "a1i.mm"
include "wel.mm"
include "ssun2.mm"
include "vsnid.mm"
include "sselii.mm"
include "lspssid.mm"
include "eldifn.mm"
include "adantl.mm"
include "ssneldd.mm"
include "nelne1.mm"
include "sylancr.mm"
include "necomd.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "eldifi.mm"
include "snssd.mm"
include "unssd.mm"
include "cbs.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elpw2.mm"
include "sylibr.mm"
include "simprd.mm"
include "syl6ss.mm"
include "ad2antrr.mm"
include "ssdifssd.mm"
include "adantrr.mm"
include "simprrr.mm"
include "cin.mm"
include "simprrl.mm"
include "nelne2.mm"
include "nelsn.mm"
include "disjsn.mm"
include "disj3.mm"
include "uneq2d.mm"
include "difundir.mm"
include "syl6reqr.mm"
include "eleqtrd.mm"
include "rsp.mm"
include "sylc.mm"
include "eldifd.mm"
include "lspsolv.mm"
include "syl13anc.mm"
include "undif1.mm"
include "ssequn2.mm"
include "syl5eq.mm"
include "expr.mm"
include "mtod.mm"
include "imnan.mm"
include "ralrimiv.mm"
include "difssd.mm"
include "lspss.mm"
include "vex.mm"
include "id.mm"
include "sneq.mm"
include "difeq2d.mm"
include "difun2.mm"
include "syl6eq.mm"
include "eleq12d.mm"
include "ralsn.mm"
include "ralun.mm"
include "jca.mm"
include "simplrr.mm"
include "psseq2.mm"
include "rspcv.mm"
include "pm2.65da.mm"
include "eq0rdv.mm"
include "ssdif0.mm"
include "eqssd.mm"
include "wb.mm"
include "islbs2.mm"
include "mpbir3and.mm"
include "reximdv2.mm"
include "mpd.mm"

theorem lbsextlem4
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cC: class C
  let cS: class S
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vt: setvar t
  let cT: class T
  let cA: class A
  assume lbsext.v: |- V = ( Base ` W )
  assume lbsext.j: |- J = ( LBasis ` W )
  assume lbsext.n: |- N = ( LSpan ` W )
  assume lbsext.w: |- ( ph -> W e. LVec )
  assume lbsext.c: |- ( ph -> C C_ V )
  assume lbsext.x: |- ( ph -> A. x e. C -. x e. ( N ` ( C \ { x } ) ) )
  assume lbsext.s: |- S = { z e. ~P V | ( C C_ z /\ A. x e. z -. x e. ( N ` ( z \ { x } ) ) ) }
  assume lbsext.k: |- ( ph -> ~P V e. dom card )

  disjoint J x
  disjoint ph x
  disjoint s x
  disjoint S s
  disjoint S x
  disjoint x z
  disjoint C x
  disjoint C z
  disjoint N x
  disjoint N z
  disjoint V x
  disjoint V z
  disjoint W x
  disjoint s z
  disjoint ph s
  disjoint m n
  disjoint m r
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m ph
  disjoint n r
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n ph
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint ph r
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint x y
  disjoint ph y
  disjoint s t
  disjoint s u
  disjoint s w
  disjoint s y
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint S t
  disjoint S u
  disjoint S w
  disjoint S y
  disjoint T m
  disjoint T n
  disjoint T r
  disjoint T v
  disjoint T w
  disjoint m z
  disjoint N m
  disjoint n z
  disjoint N n
  disjoint u z
  disjoint N u
  disjoint w z
  disjoint N w
  disjoint y z
  disjoint N y
  disjoint V u
  disjoint V w
  disjoint W m
  disjoint W n
  disjoint W r
  disjoint W u
  disjoint W v
  disjoint W w
  disjoint m s
  disjoint m t
  disjoint A m
  disjoint n s
  disjoint n t
  disjoint A n
  disjoint A s
  disjoint t z
  disjoint A t
  disjoint A u
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( ph -> E. s e. J C C_ s )

  proof
    wph
    vs
    cv
    #
    vt
    cv
    #
    wpss
    #
    wn
    #
    vt
    cS
    wral
    #
    vs
    cS
    wrex
    #
    cC
    @0
    wss
    #
    vs
    cJ
    wrex
    wph
    cS
    ccrd
    cdm
    #
    wcel
    #
    cS
    c0
    wne
    vy
    cv
    #
    cS
    wss
    #
    @9
    c0
    wne
    #
    @9
    crpss
    wor
    #
    w3a
    #
    @9
    cuni
    cS
    wcel
    #
    wi
    #
    vy
    wal
    @5
    wph
    cV
    cpw
    #
    @7
    wcel
    cS
    @16
    wss
    @8
    lbsext.k
    cS
    cC
    vz
    cv
    #
    wss
    #
    vx
    cv
    #
    @17
    @19
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @17
    wral
    #
    wa
    #
    vz
    @16
    crab
    @16
    lbsext.s
    @26
    vz
    @16
    ssrab2
    eqsstri
    @16
    cS
    ssnum
    sylancl
    wph
    vx
    vz
    cC
    cS
    cJ
    cN
    cV
    cW
    lbsext.v
    lbsext.j
    lbsext.n
    lbsext.w
    lbsext.c
    lbsext.x
    lbsext.s
    lbsextlem1
    wph
    @15
    vy
    wph
    @13
    @14
    wph
    @13
    wa
    vx
    vz
    vu
    @9
    cC
    cW
    clss
    cfv
    #
    cS
    vu
    @9
    vu
    cv
    @20
    cdif
    cN
    cfv
    ciun
    #
    cJ
    cN
    cV
    cW
    lbsext.v
    lbsext.j
    lbsext.n
    wph
    cW
    clvec
    wcel
    #
    @13
    lbsext.w
    adantr
    wph
    cC
    cV
    wss
    @13
    lbsext.c
    adantr
    wph
    @19
    cC
    @20
    cdif
    cN
    cfv
    wcel
    wn
    vx
    cC
    wral
    @13
    lbsext.x
    adantr
    lbsext.s
    @27
    eqid
    #
    wph
    @10
    @11
    @12
    simpr1
    wph
    @10
    @11
    @12
    simpr2
    wph
    @10
    @11
    @12
    simpr3
    @28
    eqid
    lbsextlem3
    ex
    alrimiv
    vs
    vt
    vy
    cS
    zornn0g
    syl3anc
    wph
    @4
    @6
    vs
    cS
    cJ
    wph
    @0
    cS
    wcel
    #
    @4
    wa
    #
    @0
    cJ
    wcel
    #
    @6
    wa
    wph
    @32
    wa
    #
    @33
    @6
    @34
    @33
    @0
    cV
    wss
    #
    @0
    cN
    cfv
    #
    cV
    wceq
    #
    @19
    @0
    @20
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @0
    wral
    #
    @34
    @0
    cV
    @34
    @0
    @16
    wcel
    #
    @6
    @42
    wa
    #
    @34
    @31
    @43
    @44
    wa
    wph
    @31
    @4
    simprl
    @26
    @44
    vz
    @0
    @16
    cS
    vz
    vs
    weq
    #
    @18
    @6
    @25
    @42
    @17
    @0
    cC
    sseq2
    @24
    @41
    vx
    @17
    @0
    @45
    @23
    @40
    @45
    @22
    @39
    @19
    @45
    @21
    @38
    cN
    @17
    @0
    @20
    difeq1
    fveq2d
    eleq2d
    notbid
    raleqbi1dv
    anbi12d
    lbsext.s
    elrab2
    sylib
    #
    simpld
    elpwid
    #
    @34
    @36
    cV
    @34
    cW
    clmod
    wcel
    #
    @35
    @36
    cV
    wss
    wph
    @48
    @32
    wph
    @29
    @48
    lbsext.w
    cW
    lveclmod
    syl
    adantr
    #
    @47
    @0
    cN
    cV
    cW
    lbsext.v
    lbsext.n
    lspssv
    syl2anc
    @34
    cV
    @36
    cdif
    #
    c0
    wceq
    cV
    @36
    wss
    @34
    vw
    @50
    @34
    vw
    cv
    #
    @50
    wcel
    #
    @0
    @0
    @51
    csn
    #
    cun
    #
    wpss
    #
    @34
    @52
    wa
    #
    @0
    @54
    wss
    #
    @0
    @54
    wne
    @55
    @57
    @56
    @0
    @53
    ssun1
    #
    a1i
    @56
    @54
    @0
    @56
    @51
    @54
    wcel
    vw
    vs
    wel
    wn
    #
    @54
    @0
    wne
    @53
    @54
    @51
    @53
    @0
    ssun2
    vw
    vsnid
    sselii
    @56
    @0
    @36
    @51
    @34
    @0
    @36
    wss
    #
    @52
    @34
    @48
    @35
    @60
    @49
    @47
    @0
    cN
    cV
    cW
    lbsext.v
    lbsext.n
    lspssid
    syl2anc
    adantr
    @52
    @51
    @36
    wcel
    #
    wn
    @34
    @51
    cV
    @36
    eldifn
    adantl
    #
    ssneldd
    #
    @51
    @54
    @0
    nelne1
    sylancr
    necomd
    @0
    @54
    df-pss
    sylanbrc
    @56
    @54
    cS
    wcel
    #
    @4
    @55
    wn
    #
    @56
    @54
    @16
    wcel
    #
    cC
    @54
    wss
    #
    @19
    @54
    @20
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vx
    @54
    wral
    #
    wa
    #
    @64
    @56
    @54
    cV
    wss
    @66
    @56
    @0
    @53
    cV
    @34
    @35
    @52
    @47
    adantr
    @56
    @51
    cV
    @52
    @51
    cV
    wcel
    #
    @34
    @51
    cV
    @36
    eldifi
    adantl
    #
    snssd
    unssd
    @54
    cV
    cV
    cW
    cbs
    cfv
    cvv
    lbsext.v
    cW
    cbs
    fvex
    eqeltri
    elpw2
    sylibr
    @56
    @67
    @72
    @56
    cC
    @0
    @54
    @34
    @6
    @52
    @34
    @6
    @42
    @34
    @43
    @44
    @46
    simprd
    #
    simpld
    #
    adantr
    @58
    syl6ss
    @56
    @71
    vx
    @0
    wral
    @71
    vx
    @53
    wral
    #
    @72
    @56
    @71
    vx
    @0
    @56
    vx
    vs
    wel
    #
    @70
    wa
    #
    wn
    @79
    @71
    wi
    @56
    @80
    @61
    @62
    @34
    @52
    @80
    @61
    @34
    @52
    @80
    wa
    #
    wa
    #
    @51
    @38
    @20
    cun
    #
    cN
    cfv
    #
    @36
    @82
    @29
    @38
    cV
    wss
    @74
    @19
    @38
    @53
    cun
    #
    cN
    cfv
    #
    @39
    cdif
    wcel
    @51
    @84
    wcel
    wph
    @29
    @32
    @81
    lbsext.w
    ad2antrr
    @82
    @0
    cV
    @20
    @34
    @35
    @81
    @47
    adantr
    ssdifssd
    @34
    @52
    @74
    @80
    @75
    adantrr
    @82
    @19
    @86
    @39
    @82
    @19
    @69
    @86
    @34
    @52
    @79
    @70
    simprrr
    @82
    @68
    @85
    cN
    @82
    @85
    @38
    @53
    @20
    cdif
    #
    cun
    @68
    @82
    @53
    @87
    @38
    @82
    @53
    @20
    cin
    c0
    wceq
    #
    @53
    @87
    wceq
    @82
    @19
    @53
    wcel
    wn
    #
    @88
    @82
    @19
    @51
    wne
    #
    @89
    @82
    @79
    @59
    @90
    @34
    @52
    @79
    @70
    simprrl
    #
    @34
    @52
    @59
    @80
    @63
    adantrr
    @19
    @51
    @0
    nelne2
    syl2anc
    @19
    @51
    nelsn
    syl
    @53
    @19
    disjsn
    sylibr
    @53
    @20
    disj3
    sylib
    uneq2d
    @0
    @53
    @20
    difundir
    syl6reqr
    fveq2d
    eleqtrd
    @82
    @42
    @79
    @41
    @34
    @42
    @81
    @34
    @6
    @42
    @76
    simprd
    #
    adantr
    @91
    @41
    vx
    @0
    rsp
    sylc
    eldifd
    @38
    @27
    cN
    cV
    cW
    @19
    @51
    lbsext.v
    @30
    lbsext.n
    lspsolv
    syl13anc
    @82
    @83
    @0
    cN
    @82
    @83
    @0
    @20
    cun
    #
    @0
    @0
    @20
    undif1
    @82
    @20
    @0
    wss
    @93
    @0
    wceq
    @82
    @19
    @0
    @91
    snssd
    @20
    @0
    ssequn2
    sylib
    syl5eq
    fveq2d
    eleqtrd
    expr
    mtod
    @79
    @70
    imnan
    sylibr
    ralrimiv
    @56
    @51
    @0
    @53
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    @78
    @56
    @95
    @36
    @51
    @34
    @95
    @36
    wss
    #
    @52
    @34
    @48
    @35
    @94
    @0
    wss
    @98
    @49
    @47
    @34
    @0
    @53
    difssd
    @94
    @0
    cN
    cV
    cW
    lbsext.v
    lbsext.n
    lspss
    syl3anc
    adantr
    @62
    ssneldd
    @71
    @97
    vx
    @51
    vw
    vex
    vx
    vw
    weq
    #
    @70
    @96
    @99
    @19
    @51
    @69
    @95
    @99
    id
    @99
    @68
    @94
    cN
    @99
    @68
    @54
    @53
    cdif
    @94
    @99
    @20
    @53
    @54
    @19
    @51
    sneq
    difeq2d
    @0
    @53
    difun2
    syl6eq
    fveq2d
    eleq12d
    notbid
    ralsn
    sylibr
    @71
    vx
    @0
    @53
    ralun
    syl2anc
    jca
    @26
    @73
    vz
    @54
    @16
    cS
    @17
    @54
    wceq
    #
    @18
    @67
    @25
    @72
    @17
    @54
    cC
    sseq2
    @24
    @71
    vx
    @17
    @54
    @100
    @23
    @70
    @100
    @22
    @69
    @19
    @100
    @21
    @68
    cN
    @17
    @54
    @20
    difeq1
    fveq2d
    eleq2d
    notbid
    raleqbi1dv
    anbi12d
    lbsext.s
    elrab2
    sylanbrc
    wph
    @31
    @4
    @52
    simplrr
    @3
    @65
    vt
    @54
    cS
    @1
    @54
    wceq
    @2
    @55
    @1
    @54
    @0
    psseq2
    notbid
    rspcv
    sylc
    pm2.65da
    eq0rdv
    cV
    @36
    ssdif0
    sylibr
    eqssd
    @92
    @34
    @29
    @33
    @35
    @37
    @42
    w3a
    wb
    wph
    @29
    @32
    lbsext.w
    adantr
    vx
    @0
    cJ
    cN
    cV
    cW
    lbsext.v
    lbsext.j
    lbsext.n
    islbs2
    syl
    mpbir3and
    @77
    jca
    ex
    reximdv2
    mpd
end
