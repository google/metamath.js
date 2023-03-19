include "wcel.mm"
include "co.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cfg.mm"
include "cflim.mm"
include "cin.mm"
include "inss2.mm"
include "minveclem4a.mm"
include "sseldi.mm"
include "wa.mm"
include "wceq.mm"
include "cds.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "minveclem4b.mm"
include "ovresd.mm"
include "syl5eq.mm"
include "cngp.mm"
include "ccph.mm"
include "cphngp.mm"
include "syl.mm"
include "eqid.mm"
include "ngpds.mm"
include "syl3anc.mm"
include "eqtrd.mm"
include "adantr.mm"
include "cr.mm"
include "cme.mm"
include "cmt.mm"
include "ngpms.mm"
include "msmet.mm"
include "3syl.mm"
include "metcl.mm"
include "minveclem4c.mm"
include "clmod.mm"
include "cphlmod.mm"
include "clss.mm"
include "wss.mm"
include "lssss.mm"
include "sselda.mm"
include "lmodvsubcl.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "wn.mm"
include "clt.mm"
include "ltnled.mm"
include "caddc.mm"
include "c2.mm"
include "cdiv.mm"
include "crab.mm"
include "ccl.mm"
include "cfil.mm"
include "cexp.mm"
include "cfbas.mm"
include "cpw.mm"
include "cvv.mm"
include "minveclem3b.mm"
include "fbsspw.mm"
include "sspwb.mm"
include "sylib.mm"
include "sstrd.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fbasweak.mm"
include "fgcl.mm"
include "ssfg.mm"
include "crp.mm"
include "cmpt.mm"
include "crn.mm"
include "cmin.mm"
include "readdcld.mm"
include "rehalfcld.mm"
include "resqcld.mm"
include "resubcld.mm"
include "cc0.mm"
include "cmul.mm"
include "ltadd1d.mm"
include "recnd.mm"
include "2timesd.mm"
include "breq1d.mm"
include "wb.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltmuldiv2.mm"
include "3bitr2d.mm"
include "cinf.mm"
include "c0.mm"
include "wne.mm"
include "minveclem1.mm"
include "simp3d.mm"
include "simp1d.mm"
include "simp2d.mm"
include "0re.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "syl6breqr.mm"
include "metge0.mm"
include "addge0d.mm"
include "divge0.mm"
include "syl21anc.mm"
include "lt2sqd.mm"
include "posdifd.mm"
include "3bitrd.mm"
include "biimpa.mm"
include "elrpd.mm"
include "syl5eqel.mm"
include "rabexg.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "elrnmpt1s.mm"
include "syl6eleqr.mm"
include "sseldd.mm"
include "ssrab2.mm"
include "oveq2i.mm"
include "ad2antrr.mm"
include "pncan3d.mm"
include "adantlr.mm"
include "le2sqd.mm"
include "bitr4d.mm"
include "rabbidva.mm"
include "rabss2.mm"
include "eqsstrd.mm"
include "filss.mm"
include "syl13anc.mm"
include "flimclsi.mm"
include "inss1.mm"
include "ccld.mm"
include "cmopn.mm"
include "cxmt.mm"
include "cxr.mm"
include "cxme.mm"
include "ngpxms.mm"
include "xmsxmet.mm"
include "rexrd.mm"
include "blcld.mm"
include "xmstopn.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"
include "cldcls.mm"
include "eleqtrd.mm"
include "elrab.mm"
include "simprbi.mm"
include "leadd2d.mm"
include "lemuldiv2.mm"
include "mp3an3.mm"
include "biimpar.mm"
include "syldan.mm"
include "ex.mm"
include "sylbird.mm"
include "pm2.18d.mm"
include "simpr.mm"
include "elrnmpt1.mm"
include "sylancl.mm"
include "infrelb.mm"
include "syl5eqbr.mm"
include "letrd.mm"
include "eqbrtrrd.mm"
include "ralrimiva.mm"

theorem minveclem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
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
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cK: class K
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
  assume minvec.p: |- P = U. ( J fLim ( X filGen F ) )
  assume minvec.t: |- T = ( ( ( ( ( A D P ) + S ) / 2 ) ^ 2 ) - ( S ^ 2 ) )

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint r x
  disjoint r y
  disjoint A r
  disjoint A x
  disjoint A y
  disjoint J r
  disjoint J x
  disjoint J y
  disjoint P x
  disjoint P y
  disjoint F x
  disjoint F y
  disjoint N x
  disjoint N y
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint U y
  disjoint X r
  disjoint X x
  disjoint X y
  disjoint Y r
  disjoint Y x
  disjoint Y y
  disjoint D r
  disjoint D x
  disjoint D y
  disjoint S r
  disjoint S x
  disjoint S y
  disjoint T r
  disjoint T y
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint .- j
  disjoint w x
  disjoint w y
  disjoint .- w
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
  disjoint y z
  disjoint A z
  disjoint J w
  disjoint F s
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint K y
  disjoint N j
  disjoint N w
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint R w
  disjoint U w
  disjoint X w
  disjoint Y j
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint D s
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D z
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint L y
  assert |- ( ph -> E. x e. Y A. y e. Y ( N ` ( A .- x ) ) <_ ( N ` ( A .- y ) ) )

  proof
    wph
    cP
    cY
    wcel
    cA
    cP
    c.mi
    co
    #
    cN
    cfv
    #
    cA
    vy
    cv
    #
    c.mi
    co
    #
    cN
    cfv
    #
    cle
    wbr
    #
    vy
    cY
    wral
    #
    cA
    vx
    cv
    #
    c.mi
    co
    #
    cN
    cfv
    #
    @4
    cle
    wbr
    #
    vy
    cY
    wral
    #
    vx
    cY
    wrex
    wph
    cJ
    cX
    cF
    cfg
    co
    #
    cflim
    co
    #
    cY
    cin
    #
    cY
    cP
    @13
    cY
    inss2
    wph
    vy
    cA
    cD
    cP
    cR
    cS
    cU
    cF
    cJ
    c.mi
    cN
    cX
    cY
    vr
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
    minvec.d
    minvec.f
    minvec.p
    minveclem4a
    #
    sseldi
    wph
    @5
    vy
    cY
    wph
    @2
    cY
    wcel
    #
    wa
    #
    cA
    cP
    cD
    co
    #
    @1
    @4
    cle
    wph
    @18
    @1
    wceq
    @16
    wph
    @18
    cA
    cP
    cU
    cds
    cfv
    #
    co
    #
    @1
    wph
    @18
    cA
    cP
    @19
    cX
    cX
    cxp
    cres
    #
    co
    @20
    cD
    @21
    cA
    cP
    minvec.d
    oveqi
    wph
    cA
    cP
    @19
    cX
    minvec.a
    wph
    vy
    cA
    cD
    cP
    cR
    cS
    cU
    cF
    cJ
    c.mi
    cN
    cX
    cY
    vr
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
    minvec.d
    minvec.f
    minvec.p
    minveclem4b
    #
    ovresd
    syl5eq
    wph
    cU
    cngp
    wcel
    #
    cA
    cX
    wcel
    #
    cP
    cX
    wcel
    #
    @20
    @1
    wceq
    wph
    cU
    ccph
    wcel
    #
    @23
    minvec.u
    cU
    cphngp
    syl
    #
    minvec.a
    @22
    cA
    cP
    @19
    cU
    c.mi
    cN
    cX
    minvec.n
    minvec.x
    minvec.m
    @19
    eqid
    ngpds
    syl3anc
    eqtrd
    adantr
    @17
    @18
    cS
    @4
    wph
    @18
    cr
    wcel
    #
    @16
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @24
    @25
    @28
    wph
    @23
    cU
    cmt
    wcel
    @29
    @27
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
    minvec.a
    @22
    cA
    cP
    cD
    cX
    metcl
    syl3anc
    #
    adantr
    wph
    cS
    cr
    wcel
    #
    @16
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
    #
    adantr
    @17
    @23
    @3
    cX
    wcel
    #
    @4
    cr
    wcel
    wph
    @23
    @16
    @27
    adantr
    @17
    cU
    clmod
    wcel
    #
    @24
    @2
    cX
    wcel
    #
    @34
    wph
    @35
    @16
    wph
    @26
    @35
    minvec.u
    cU
    cphlmod
    syl
    adantr
    wph
    @24
    @16
    minvec.a
    adantr
    wph
    cY
    cX
    @2
    wph
    cY
    cU
    clss
    cfv
    #
    wcel
    #
    cY
    cX
    wss
    #
    minvec.y
    @37
    cY
    cX
    cU
    minvec.x
    @37
    eqid
    lssss
    syl
    #
    sselda
    #
    c.mi
    cX
    cU
    cA
    @2
    minvec.x
    minvec.m
    lmodvsubcl
    syl3anc
    @3
    cU
    cN
    cX
    minvec.x
    minvec.n
    nmcl
    syl2anc
    wph
    @18
    cS
    cle
    wbr
    #
    @16
    wph
    @42
    wph
    @42
    wn
    cS
    @18
    clt
    wbr
    #
    @42
    wph
    cS
    @18
    @33
    @31
    ltnled
    wph
    @43
    @42
    wph
    @43
    @18
    @18
    cS
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cle
    wbr
    #
    @42
    wph
    @43
    wa
    #
    cP
    cA
    @2
    cD
    co
    #
    @45
    cle
    wbr
    #
    vy
    cX
    crab
    #
    wcel
    #
    @46
    @47
    cP
    @50
    cJ
    ccl
    cfv
    cfv
    #
    @50
    @47
    @13
    @52
    cP
    @47
    @50
    @12
    wcel
    #
    @13
    @52
    wss
    @47
    @12
    cX
    cfil
    cfv
    wcel
    #
    @48
    c2
    cexp
    co
    #
    cS
    c2
    cexp
    co
    #
    cT
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
    @12
    wcel
    @50
    cX
    wss
    #
    @59
    @50
    wss
    @53
    @47
    cF
    cX
    cfbas
    cfv
    wcel
    #
    @54
    wph
    @61
    @43
    wph
    cF
    cY
    cfbas
    cfv
    wcel
    #
    cF
    cX
    cpw
    #
    wss
    cX
    cvv
    wcel
    #
    @61
    wph
    vy
    cA
    cD
    cR
    cS
    cU
    cF
    cJ
    c.mi
    cN
    cX
    cY
    vr
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
    minvec.d
    minvec.f
    minveclem3b
    #
    wph
    cF
    cY
    cpw
    #
    @63
    wph
    @62
    cF
    @66
    wss
    @65
    cY
    cF
    fbsspw
    syl
    wph
    @39
    @66
    @63
    wss
    @40
    cY
    cX
    sspwb
    sylib
    sstrd
    @64
    wph
    cX
    cU
    cbs
    cfv
    cvv
    minvec.x
    cU
    cbs
    fvex
    eqeltri
    a1i
    cF
    cvv
    cY
    cX
    fbasweak
    syl3anc
    adantr
    #
    cF
    cX
    fgcl
    syl
    @47
    cF
    @12
    @59
    @47
    @61
    cF
    @12
    wss
    @67
    cF
    cX
    ssfg
    syl
    @47
    @59
    vr
    crp
    @55
    @56
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
    cF
    @47
    cT
    crp
    wcel
    @59
    cvv
    wcel
    #
    @59
    @73
    wcel
    @47
    cT
    @45
    c2
    cexp
    co
    #
    @56
    cmin
    co
    #
    crp
    minvec.t
    @47
    @76
    wph
    @76
    cr
    wcel
    @43
    wph
    @75
    @56
    wph
    @45
    wph
    @44
    wph
    @18
    cS
    @31
    @33
    readdcld
    #
    rehalfcld
    #
    resqcld
    #
    wph
    cS
    @33
    resqcld
    #
    resubcld
    adantr
    wph
    @43
    cc0
    @76
    clt
    wbr
    #
    wph
    @43
    cS
    @45
    clt
    wbr
    #
    @56
    @75
    clt
    wbr
    @81
    wph
    @43
    cS
    cS
    caddc
    co
    #
    @44
    clt
    wbr
    c2
    cS
    cmul
    co
    #
    @44
    clt
    wbr
    #
    @82
    wph
    cS
    @18
    cS
    @33
    @31
    @33
    ltadd1d
    wph
    @84
    @83
    @44
    clt
    wph
    cS
    wph
    cS
    @33
    recnd
    2timesd
    breq1d
    wph
    @32
    @44
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @85
    @82
    wb
    @33
    @77
    @89
    wph
    @87
    @88
    2re
    2pos
    pm3.2i
    #
    a1i
    #
    cS
    @44
    c2
    ltmuldiv2
    syl3anc
    3bitr2d
    wph
    cS
    @45
    @33
    @78
    wph
    cc0
    cR
    cr
    clt
    cinf
    #
    cS
    cle
    wph
    cc0
    @92
    cle
    wbr
    #
    cc0
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
    wph
    cR
    cr
    wss
    #
    cR
    c0
    wne
    #
    @96
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
    simp3d
    #
    wph
    @97
    @98
    @7
    @94
    cle
    wbr
    #
    vw
    cR
    wral
    #
    vx
    cr
    wrex
    #
    cc0
    cr
    wcel
    #
    @93
    @96
    wb
    wph
    @97
    @98
    @96
    @99
    simp1d
    #
    wph
    @97
    @98
    @96
    @99
    simp2d
    wph
    @104
    @96
    @103
    0re
    @100
    @102
    @96
    vx
    cc0
    cr
    @7
    cc0
    wceq
    @101
    @95
    vw
    cR
    @7
    cc0
    @94
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    #
    @104
    wph
    0re
    a1i
    vx
    vw
    vw
    cR
    cc0
    infregelb
    syl31anc
    mpbird
    minvec.s
    syl6breqr
    #
    wph
    @86
    cc0
    @44
    cle
    wbr
    @89
    cc0
    @45
    cle
    wbr
    #
    @77
    wph
    @18
    cS
    @31
    @33
    wph
    @29
    @24
    @25
    cc0
    @18
    cle
    wbr
    @30
    minvec.a
    @22
    cA
    cP
    cD
    cX
    metge0
    syl3anc
    @107
    addge0d
    @91
    @44
    c2
    divge0
    syl21anc
    #
    lt2sqd
    wph
    @56
    @75
    @80
    @79
    posdifd
    3bitrd
    biimpa
    elrpd
    syl5eqel
    @47
    @38
    @74
    wph
    @38
    @43
    minvec.y
    adantr
    @58
    vy
    cY
    @37
    rabexg
    syl
    vr
    crp
    @71
    @59
    cT
    @72
    cvv
    @72
    eqid
    @68
    cT
    wceq
    #
    @70
    @58
    vy
    cY
    @110
    @69
    @57
    @55
    cle
    @68
    cT
    @56
    caddc
    oveq2
    breq2d
    rabbidv
    elrnmpt1s
    syl2anc
    minvec.f
    syl6eleqr
    sseldd
    @60
    @47
    @49
    vy
    cX
    ssrab2
    a1i
    @47
    @59
    @49
    vy
    cY
    crab
    #
    @50
    @47
    @58
    @49
    vy
    cY
    @47
    @16
    wa
    #
    @58
    @55
    @75
    cle
    wbr
    @49
    @112
    @57
    @75
    @55
    cle
    @112
    @57
    @56
    @76
    caddc
    co
    @75
    cT
    @76
    @56
    caddc
    minvec.t
    oveq2i
    @112
    @56
    @75
    @112
    @56
    wph
    @56
    cr
    wcel
    @43
    @16
    @80
    ad2antrr
    recnd
    @112
    @75
    @112
    @45
    wph
    @45
    cr
    wcel
    #
    @43
    @16
    @78
    ad2antrr
    #
    resqcld
    recnd
    pncan3d
    syl5eq
    breq2d
    @112
    @48
    @45
    @112
    @29
    @24
    @36
    @48
    cr
    wcel
    wph
    @29
    @43
    @16
    @30
    ad2antrr
    #
    wph
    @24
    @43
    @16
    minvec.a
    ad2antrr
    #
    wph
    @16
    @36
    @43
    @41
    adantlr
    #
    cA
    @2
    cD
    cX
    metcl
    syl3anc
    @114
    @112
    @29
    @24
    @36
    cc0
    @48
    cle
    wbr
    @115
    @116
    @117
    cA
    @2
    cD
    cX
    metge0
    syl3anc
    wph
    @108
    @43
    @16
    @109
    ad2antrr
    le2sqd
    bitr4d
    rabbidva
    @47
    @39
    @111
    @50
    wss
    wph
    @39
    @43
    @40
    adantr
    @49
    vy
    cY
    cX
    rabss2
    syl
    eqsstrd
    @59
    @50
    @12
    cX
    filss
    syl13anc
    @50
    @12
    cJ
    flimclsi
    syl
    wph
    cP
    @13
    wcel
    @43
    wph
    @14
    @13
    cP
    @13
    cY
    inss1
    @15
    sseldi
    adantr
    sseldd
    @47
    @50
    cJ
    ccld
    cfv
    #
    wcel
    @52
    @50
    wceq
    @47
    @50
    cD
    cmopn
    cfv
    #
    ccld
    cfv
    #
    @118
    @47
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @24
    @45
    cxr
    wcel
    @50
    @120
    wcel
    wph
    @121
    @43
    wph
    @23
    cU
    cxme
    wcel
    #
    @121
    @27
    cU
    ngpxms
    #
    cD
    cU
    cX
    minvec.x
    minvec.d
    xmsxmet
    3syl
    adantr
    wph
    @24
    @43
    minvec.a
    adantr
    @47
    @45
    wph
    @113
    @43
    @78
    adantr
    rexrd
    vy
    cD
    cA
    @45
    @50
    @119
    cX
    @119
    eqid
    @50
    eqid
    blcld
    syl3anc
    @47
    cJ
    @119
    ccld
    wph
    cJ
    @119
    wceq
    #
    @43
    wph
    @23
    @122
    @124
    @27
    @123
    cD
    cJ
    cU
    cX
    minvec.j
    minvec.x
    minvec.d
    xmstopn
    3syl
    adantr
    fveq2d
    eleqtrrd
    @50
    cJ
    cldcls
    syl
    eleqtrd
    @51
    @25
    @46
    @49
    @46
    vy
    cP
    cX
    @2
    cP
    wceq
    @48
    @18
    @45
    cle
    @2
    cP
    cA
    cD
    oveq2
    breq1d
    elrab
    simprbi
    syl
    wph
    @42
    @46
    wph
    @42
    @18
    @18
    caddc
    co
    #
    @44
    cle
    wbr
    c2
    @18
    cmul
    co
    #
    @44
    cle
    wbr
    #
    @46
    wph
    @18
    cS
    @18
    @31
    @33
    @31
    leadd2d
    wph
    @126
    @125
    @44
    cle
    wph
    @18
    wph
    @18
    @31
    recnd
    2timesd
    breq1d
    wph
    @28
    @86
    @127
    @46
    wb
    #
    @31
    @77
    @28
    @86
    @89
    @128
    @90
    @18
    @44
    c2
    lemuldiv2
    mp3an3
    syl2anc
    3bitr2d
    biimpar
    syldan
    ex
    sylbird
    pm2.18d
    adantr
    @17
    cS
    @92
    @4
    cle
    minvec.s
    @17
    @97
    @103
    @4
    cR
    wcel
    @92
    @4
    cle
    wbr
    wph
    @97
    @16
    @105
    adantr
    wph
    @103
    @16
    @106
    adantr
    @17
    @4
    vy
    cY
    @4
    cmpt
    #
    crn
    #
    cR
    @17
    @16
    @4
    cvv
    wcel
    @4
    @130
    wcel
    wph
    @16
    simpr
    @3
    cN
    fvex
    vy
    cY
    @4
    @129
    cvv
    @129
    eqid
    elrnmpt1
    sylancl
    minvec.r
    syl6eleqr
    vx
    vw
    @4
    cR
    infrelb
    syl3anc
    syl5eqbr
    letrd
    eqbrtrrd
    ralrimiva
    @11
    @6
    vx
    cP
    cY
    @7
    cP
    wceq
    #
    @10
    @5
    vy
    cY
    @131
    @9
    @1
    @4
    cle
    @131
    @8
    @0
    cN
    @7
    cP
    cA
    c.mi
    oveq2
    fveq2d
    breq1d
    ralbidv
    rspcev
    syl2anc
end
