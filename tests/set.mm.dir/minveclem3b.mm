include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wnel.mm"
include "cv.mm"
include "cin.mm"
include "wral.mm"
include "w3a.mm"
include "crp.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "wf.mm"
include "wa.mm"
include "ssrab2.mm"
include "clss.mm"
include "wb.mm"
include "adantr.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbiri.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl5eqss.mm"
include "cdm.mm"
include "c1.mm"
include "1rp.mm"
include "dmmptd.mm"
include "syl5eleqr.mm"
include "ne0i.mm"
include "wceq.mm"
include "dm0rn0.mm"
include "eqeq1i.mm"
include "bitr4i.mm"
include "necon3bii.mm"
include "sylib.mm"
include "wn.mm"
include "wrex.mm"
include "csqrt.mm"
include "clt.mm"
include "cr.mm"
include "minveclem4c.mm"
include "resqcld.mm"
include "ltaddrp.mm"
include "sylan.mm"
include "rpre.mm"
include "adantl.mm"
include "readdcld.mm"
include "recnd.mm"
include "sqsqrtd.mm"
include "breqtrrd.mm"
include "cinf.mm"
include "cc0.mm"
include "minveclem1.mm"
include "simp1d.mm"
include "simp2d.mm"
include "0re.mm"
include "simp3d.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "infrecl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "0red.mm"
include "sqge0d.mm"
include "lelttrd.mm"
include "ltled.mm"
include "resqrtcld.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "syl6breqr.mm"
include "sqrtge0d.mm"
include "lt2sqd.mm"
include "ltnled.mm"
include "mpbid.mm"
include "breq2i.mm"
include "raleqi.mm"
include "cvv.mm"
include "fvex.mm"
include "rgenw.mm"
include "breq2.mm"
include "ralrnmpt.mm"
include "ax-mp.mm"
include "bitri.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "mtbid.mm"
include "rexnal.mm"
include "sylibr.mm"
include "cme.mm"
include "cngp.mm"
include "cmt.mm"
include "ccph.mm"
include "cphngp.mm"
include "ngpms.mm"
include "msmet.mm"
include "3syl.mm"
include "ad2antrr.mm"
include "lssss.mm"
include "sselda.mm"
include "metcl.mm"
include "metge0.mm"
include "le2sqd.mm"
include "cds.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "ovresd.mm"
include "syl5eq.mm"
include "ngpds.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "breq1d.mm"
include "3bitr3d.mm"
include "notbid.mm"
include "letrid.mm"
include "ord.mm"
include "sylbid.mm"
include "reximdva.mm"
include "mpd.mm"
include "rabn0.mm"
include "necomd.mm"
include "neneqd.mm"
include "nrexdv.mm"
include "eleq2i.mm"
include "0ex.mm"
include "elrnmpt.mm"
include "sylnibr.mm"
include "df-nel.mm"
include "cmin.mm"
include "lesubadd2d.mm"
include "rabbidva.mm"
include "mpteq2dva.mm"
include "rneqd.mm"
include "syl6reqr.mm"
include "eleq2d.mm"
include "vex.mm"
include "rabbidv.mm"
include "cbvmptv.mm"
include "anbi12d.mm"
include "reeanv.mm"
include "cif.mm"
include "resubcld.mm"
include "simplrl.mm"
include "rpred.mm"
include "simplrr.mm"
include "lemin.mm"
include "ifcl.mm"
include "rabexg.mm"
include "elrnmpt1s.mm"
include "syl2anc.mm"
include "eleqtrrd.mm"
include "eqeltrrd.mm"
include "ineq12.mm"
include "inrab.mm"
include "syl6eq.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "inex1.mm"
include "pwid.mm"
include "inelcm.mm"
include "mpan2.mm"
include "syl6.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "ralrimivv.mm"
include "3jca.mm"
include "isfbas.mm"
include "mpbir2and.mm"

theorem minveclem3b
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cJ: class J
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let vj: setvar j
  let vw: setvar w
  let vx: setvar x
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cP: class P
  let cK: class K
  let cT: class T
  let cL: class L
  assume minvec.x: |- X = ( Base ` U )
  assume minvec.m: |- .- = ( -g ` U )
  assume minvec.n: |- N = ( norm ` U )
  assume minvec.u: |- ( ph -> U e. CPreHil )
  assume minvec.y: |- ( ph -> Y e. ( LSubSp ` U ) )
  assume minvec.w: |- ( ph -> ( U |`s Y ) e. CMetSp )
  assume minvec.a: |- ( ph -> A e. X )
  assume minvec.j: |- J = ( TopOpen ` U )
  assume minvec.r: |- R = ran ( y e. Y |-> ( N ` ( A .- y ) ) )
  assume minvec.s: |- S = inf ( R , RR , < )
  assume minvec.d: |- D = ( ( dist ` U ) |` ( X X. X ) )
  assume minvec.f: |- F = ran ( r e. RR+ |-> { y e. Y | ( ( A D y ) ^ 2 ) <_ ( ( S ^ 2 ) + r ) } )

  disjoint .- y
  disjoint r y
  disjoint A r
  disjoint A y
  disjoint J r
  disjoint J y
  disjoint F y
  disjoint N y
  disjoint ph r
  disjoint ph y
  disjoint R y
  disjoint U y
  disjoint X r
  disjoint X y
  disjoint Y r
  disjoint Y y
  disjoint D r
  disjoint D y
  disjoint S r
  disjoint S y
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint .- j
  disjoint w x
  disjoint w y
  disjoint .- w
  disjoint x y
  disjoint .- x
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j z
  disjoint A j
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r z
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint J w
  disjoint J x
  disjoint P x
  disjoint P y
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint F x
  disjoint K y
  disjoint N j
  disjoint N w
  disjoint N x
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint R w
  disjoint R x
  disjoint U w
  disjoint U x
  disjoint X w
  disjoint X x
  disjoint Y j
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y z
  disjoint D s
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D z
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S z
  disjoint T r
  disjoint T y
  disjoint L y
  assert |- ( ph -> F e. ( fBas ` Y ) )

  proof
    wph
    cF
    cY
    cfbas
    cfv
    wcel
    #
    cF
    cY
    cpw
    #
    wss
    #
    cF
    c0
    wne
    #
    c0
    cF
    wnel
    #
    cF
    vu
    cv
    #
    vv
    cv
    #
    cin
    #
    cpw
    #
    cin
    c0
    wne
    #
    vv
    cF
    wral
    vu
    cF
    wral
    #
    w3a
    #
    wph
    cF
    vr
    crp
    cA
    vy
    cv
    #
    cD
    co
    #
    c2
    cexp
    co
    #
    cS
    c2
    cexp
    co
    #
    vr
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    cY
    crab
    #
    cmpt
    #
    crn
    #
    @1
    minvec.f
    wph
    crp
    @1
    @20
    wf
    @21
    @1
    wss
    wph
    vr
    crp
    @19
    @1
    @20
    wph
    @16
    crp
    wcel
    #
    wa
    #
    @19
    @1
    wcel
    #
    @19
    cY
    wss
    #
    @18
    vy
    cY
    ssrab2
    @23
    cY
    cU
    clss
    cfv
    #
    wcel
    #
    @24
    @25
    wb
    wph
    @27
    @22
    minvec.y
    adantr
    #
    @19
    cY
    @26
    elpw2g
    syl
    mpbiri
    #
    @20
    eqid
    #
    fmptd
    crp
    @1
    @20
    frn
    syl
    syl5eqss
    wph
    @3
    @4
    @10
    wph
    @20
    cdm
    #
    c0
    wne
    #
    @3
    wph
    c1
    @31
    wcel
    @32
    wph
    c1
    crp
    @31
    1rp
    wph
    vr
    @20
    crp
    @19
    @1
    @30
    @29
    dmmptd
    syl5eleqr
    @31
    c1
    ne0i
    syl
    @31
    c0
    cF
    c0
    @31
    c0
    wceq
    @21
    c0
    wceq
    cF
    c0
    wceq
    @20
    dm0rn0
    cF
    @21
    c0
    minvec.f
    eqeq1i
    bitr4i
    necon3bii
    sylib
    wph
    c0
    cF
    wcel
    #
    wn
    @4
    wph
    c0
    @19
    wceq
    #
    vr
    crp
    wrex
    #
    @33
    wph
    @34
    vr
    crp
    @23
    c0
    @19
    @23
    @19
    c0
    @23
    @18
    vy
    cY
    wrex
    #
    @19
    c0
    wne
    @23
    @17
    csqrt
    cfv
    #
    cA
    @12
    c.mi
    co
    #
    cN
    cfv
    #
    cle
    wbr
    #
    wn
    #
    vy
    cY
    wrex
    #
    @36
    @23
    @40
    vy
    cY
    wral
    #
    wn
    @42
    @23
    @37
    cS
    cle
    wbr
    #
    @43
    @23
    cS
    @37
    clt
    wbr
    #
    @44
    wn
    @23
    @45
    @15
    @37
    c2
    cexp
    co
    #
    clt
    wbr
    @23
    @15
    @17
    @46
    clt
    wph
    @15
    cr
    wcel
    #
    @22
    @15
    @17
    clt
    wbr
    wph
    cS
    wph
    vy
    cA
    cR
    cS
    cU
    cJ
    c.mi
    cN
    cX
    cY
    minvec.x
    minvec.m
    minvec.n
    minvec.u
    minvec.y
    minvec.w
    minvec.a
    minvec.j
    minvec.r
    minvec.s
    minveclem4c
    resqcld
    #
    @15
    @16
    ltaddrp
    sylan
    #
    @23
    @17
    @23
    @17
    @23
    @15
    @16
    wph
    @47
    @22
    @48
    adantr
    #
    @22
    @16
    cr
    wcel
    #
    wph
    @16
    rpre
    adantl
    #
    readdcld
    #
    recnd
    sqsqrtd
    #
    breqtrrd
    @23
    cS
    @37
    @23
    cS
    cR
    cr
    clt
    cinf
    #
    cr
    minvec.s
    @23
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    @12
    vw
    cv
    #
    cle
    wbr
    #
    vw
    cR
    wral
    #
    vy
    cr
    wrex
    #
    @55
    cr
    wcel
    wph
    @56
    @22
    wph
    @56
    @57
    cc0
    @58
    cle
    wbr
    #
    vw
    cR
    wral
    #
    wph
    vy
    vw
    cA
    cR
    cU
    cJ
    c.mi
    cN
    cX
    cY
    minvec.x
    minvec.m
    minvec.n
    minvec.u
    minvec.y
    minvec.w
    minvec.a
    minvec.j
    minvec.r
    minveclem1
    #
    simp1d
    adantr
    #
    wph
    @57
    @22
    wph
    @56
    @57
    @63
    @64
    simp2d
    adantr
    #
    wph
    @61
    @22
    wph
    cc0
    cr
    wcel
    #
    @63
    @61
    0re
    wph
    @56
    @57
    @63
    @64
    simp3d
    #
    @60
    @63
    vy
    cc0
    cr
    @12
    cc0
    wceq
    @59
    @62
    vw
    cR
    @12
    cc0
    @58
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    adantr
    #
    vy
    vw
    cR
    infrecl
    syl3anc
    syl5eqel
    #
    @23
    @17
    @53
    @23
    cc0
    @17
    @23
    0red
    #
    @53
    @23
    cc0
    @15
    @17
    @71
    @50
    @53
    @23
    cS
    @70
    sqge0d
    @49
    lelttrd
    ltled
    #
    resqrtcld
    #
    @23
    cc0
    @55
    cS
    cle
    @23
    cc0
    @55
    cle
    wbr
    #
    @63
    wph
    @63
    @22
    @68
    adantr
    @23
    @56
    @57
    @61
    @67
    @74
    @63
    wb
    @65
    @66
    @69
    @71
    vy
    vw
    vw
    cR
    cc0
    infregelb
    syl31anc
    mpbird
    minvec.s
    syl6breqr
    @23
    @17
    @53
    @72
    sqrtge0d
    #
    lt2sqd
    mpbird
    @23
    cS
    @37
    @70
    @73
    ltnled
    mpbid
    @44
    @37
    @55
    cle
    wbr
    #
    @23
    @43
    cS
    @55
    @37
    cle
    minvec.s
    breq2i
    @23
    @76
    @37
    @58
    cle
    wbr
    #
    vw
    cR
    wral
    #
    @43
    @23
    @56
    @57
    @61
    @37
    cr
    wcel
    #
    @76
    @78
    wb
    @65
    @66
    @69
    @73
    vy
    vw
    vw
    cR
    @37
    infregelb
    syl31anc
    @78
    @77
    vw
    vy
    cY
    @39
    cmpt
    #
    crn
    #
    wral
    #
    @43
    @77
    vw
    cR
    @81
    minvec.r
    raleqi
    @39
    cvv
    wcel
    #
    vy
    cY
    wral
    @82
    @43
    wb
    @83
    vy
    cY
    @38
    cN
    fvex
    rgenw
    @77
    @40
    vy
    vw
    cY
    @39
    @80
    cvv
    @80
    eqid
    @58
    @39
    @37
    cle
    breq2
    ralrnmpt
    ax-mp
    bitri
    syl6bb
    syl5bb
    mtbid
    @40
    vy
    cY
    rexnal
    sylibr
    @23
    @41
    @18
    vy
    cY
    @23
    @12
    cY
    wcel
    #
    wa
    #
    @41
    @17
    @14
    cle
    wbr
    #
    wn
    @18
    @85
    @40
    @86
    @85
    @37
    @13
    cle
    wbr
    @46
    @14
    cle
    wbr
    @40
    @86
    @85
    @37
    @13
    @23
    @79
    @84
    @73
    adantr
    @85
    cD
    cX
    cme
    cfv
    wcel
    #
    cA
    cX
    wcel
    #
    @12
    cX
    wcel
    #
    @13
    cr
    wcel
    #
    wph
    @87
    @22
    @84
    wph
    cU
    cngp
    wcel
    #
    cU
    cmt
    wcel
    @87
    wph
    cU
    ccph
    wcel
    @91
    minvec.u
    cU
    cphngp
    syl
    #
    cU
    ngpms
    cD
    cU
    cX
    minvec.x
    minvec.d
    msmet
    3syl
    #
    ad2antrr
    #
    wph
    @88
    @22
    @84
    minvec.a
    ad2antrr
    #
    @23
    cY
    cX
    @12
    @23
    @27
    cY
    cX
    wss
    #
    @28
    @26
    cY
    cX
    cU
    minvec.x
    @26
    eqid
    lssss
    #
    syl
    sselda
    #
    cA
    @12
    cD
    cX
    metcl
    #
    syl3anc
    #
    @23
    cc0
    @37
    cle
    wbr
    @84
    @75
    adantr
    @85
    @87
    @88
    @89
    cc0
    @13
    cle
    wbr
    @94
    @95
    @98
    cA
    @12
    cD
    cX
    metge0
    syl3anc
    le2sqd
    @85
    @13
    @39
    @37
    cle
    @85
    @13
    cA
    @12
    cU
    cds
    cfv
    #
    co
    #
    @39
    @85
    @13
    cA
    @12
    @101
    cX
    cX
    cxp
    cres
    #
    co
    @102
    cD
    @103
    cA
    @12
    minvec.d
    oveqi
    @85
    cA
    @12
    @101
    cX
    @95
    @98
    ovresd
    syl5eq
    @85
    @91
    @88
    @89
    @102
    @39
    wceq
    wph
    @91
    @22
    @84
    @92
    ad2antrr
    @95
    @98
    cA
    @12
    @101
    cU
    c.mi
    cN
    cX
    minvec.n
    minvec.x
    minvec.m
    @101
    eqid
    ngpds
    syl3anc
    eqtrd
    breq2d
    @85
    @46
    @17
    @14
    cle
    @23
    @46
    @17
    wceq
    @84
    @54
    adantr
    breq1d
    3bitr3d
    notbid
    @85
    @86
    @18
    @85
    @17
    @14
    @23
    @17
    cr
    wcel
    @84
    @53
    adantr
    @85
    @13
    @100
    resqcld
    #
    letrid
    ord
    sylbid
    reximdva
    mpd
    @18
    vy
    cY
    rabn0
    sylibr
    necomd
    neneqd
    nrexdv
    @33
    c0
    @21
    wcel
    #
    @35
    cF
    @21
    c0
    minvec.f
    eleq2i
    c0
    cvv
    wcel
    @105
    @35
    wb
    0ex
    vr
    crp
    @19
    c0
    @20
    cvv
    @30
    elrnmpt
    ax-mp
    bitri
    sylnibr
    c0
    cF
    df-nel
    sylibr
    wph
    @9
    vu
    vv
    cF
    cF
    wph
    @5
    cF
    wcel
    #
    @6
    cF
    wcel
    #
    wa
    @5
    @14
    @15
    cmin
    co
    #
    vs
    cv
    #
    cle
    wbr
    #
    vy
    cY
    crab
    #
    wceq
    #
    vs
    crp
    wrex
    #
    @6
    @108
    vt
    cv
    #
    cle
    wbr
    #
    vy
    cY
    crab
    #
    wceq
    #
    vt
    crp
    wrex
    #
    wa
    #
    @9
    wph
    @106
    @113
    @107
    @118
    wph
    @106
    @5
    vr
    crp
    @108
    @16
    cle
    wbr
    #
    vy
    cY
    crab
    #
    cmpt
    #
    crn
    #
    wcel
    #
    @113
    wph
    cF
    @123
    @5
    wph
    @123
    @21
    cF
    wph
    @122
    @20
    wph
    vr
    crp
    @121
    @19
    @23
    @120
    @18
    vy
    cY
    @85
    @14
    @15
    @16
    @104
    @85
    cS
    @23
    cS
    cr
    wcel
    @84
    @70
    adantr
    resqcld
    @23
    @51
    @84
    @52
    adantr
    lesubadd2d
    rabbidva
    mpteq2dva
    rneqd
    minvec.f
    syl6reqr
    #
    eleq2d
    @5
    cvv
    wcel
    @124
    @113
    wb
    vu
    vex
    #
    vs
    crp
    @111
    @5
    @122
    cvv
    vr
    vs
    crp
    @121
    @111
    @16
    @109
    wceq
    @120
    @110
    vy
    cY
    @16
    @109
    @108
    cle
    breq2
    rabbidv
    cbvmptv
    elrnmpt
    ax-mp
    syl6bb
    wph
    @107
    @6
    @123
    wcel
    #
    @118
    wph
    cF
    @123
    @6
    @125
    eleq2d
    @6
    cvv
    wcel
    @127
    @118
    wb
    vv
    vex
    vt
    crp
    @116
    @6
    @122
    cvv
    vr
    vt
    crp
    @121
    @116
    @16
    @114
    wceq
    @120
    @115
    vy
    cY
    @16
    @114
    @108
    cle
    breq2
    rabbidv
    cbvmptv
    elrnmpt
    ax-mp
    syl6bb
    anbi12d
    @119
    @112
    @117
    wa
    #
    vt
    crp
    wrex
    vs
    crp
    wrex
    wph
    @9
    @112
    @117
    vs
    vt
    crp
    crp
    reeanv
    wph
    @128
    @9
    vs
    vt
    crp
    crp
    wph
    @109
    crp
    wcel
    #
    @114
    crp
    wcel
    #
    wa
    #
    wa
    #
    @128
    @7
    cF
    wcel
    #
    @9
    @132
    @133
    @128
    @110
    @115
    wa
    #
    vy
    cY
    crab
    #
    cF
    wcel
    @132
    @108
    @109
    @114
    cle
    wbr
    #
    @109
    @114
    cif
    #
    cle
    wbr
    #
    vy
    cY
    crab
    #
    @135
    cF
    @132
    @138
    @134
    vy
    cY
    @132
    @84
    wa
    #
    @108
    cr
    wcel
    @109
    cr
    wcel
    @114
    cr
    wcel
    @138
    @134
    wb
    @140
    @14
    @15
    @140
    @13
    @140
    @87
    @88
    @89
    @90
    wph
    @87
    @131
    @84
    @93
    ad2antrr
    wph
    @88
    @131
    @84
    minvec.a
    ad2antrr
    @132
    cY
    cX
    @12
    wph
    @96
    @131
    wph
    @27
    @96
    minvec.y
    @97
    syl
    adantr
    sselda
    @99
    syl3anc
    resqcld
    wph
    @47
    @131
    @84
    @48
    ad2antrr
    resubcld
    @140
    @109
    wph
    @129
    @130
    @84
    simplrl
    rpred
    @140
    @114
    wph
    @129
    @130
    @84
    simplrr
    rpred
    @108
    @109
    @114
    lemin
    syl3anc
    rabbidva
    @132
    @139
    @123
    cF
    @132
    @137
    crp
    wcel
    #
    @139
    cvv
    wcel
    #
    @139
    @123
    wcel
    @131
    @141
    wph
    @136
    @109
    @114
    crp
    ifcl
    adantl
    @132
    @27
    @142
    wph
    @27
    @131
    minvec.y
    adantr
    @138
    vy
    cY
    @26
    rabexg
    syl
    vr
    crp
    @121
    @139
    @137
    @122
    cvv
    @122
    eqid
    @16
    @137
    wceq
    @120
    @138
    vy
    cY
    @16
    @137
    @108
    cle
    breq2
    rabbidv
    elrnmpt1s
    syl2anc
    wph
    cF
    @123
    wceq
    @131
    @125
    adantr
    eleqtrrd
    eqeltrrd
    @128
    @7
    @135
    cF
    @128
    @7
    @111
    @116
    cin
    @135
    @5
    @111
    @6
    @116
    ineq12
    @110
    @115
    vy
    cY
    inrab
    syl6eq
    eleq1d
    syl5ibrcom
    @133
    @7
    @8
    wcel
    @9
    @7
    @5
    @6
    @126
    inex1
    pwid
    @7
    cF
    @8
    inelcm
    mpan2
    syl6
    rexlimdvva
    syl5bir
    sylbid
    ralrimivv
    3jca
    wph
    @27
    @0
    @2
    @11
    wa
    wb
    minvec.y
    vu
    vv
    @26
    cY
    cF
    isfbas
    syl
    mpbir2and
end
