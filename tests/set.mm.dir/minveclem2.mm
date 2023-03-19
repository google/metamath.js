include "co.mm"
include "c2.mm"
include "cexp.mm"
include "c4.mm"
include "cmul.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "c1.mm"
include "cdiv.mm"
include "cplusg.mm"
include "cfv.mm"
include "cvsca.mm"
include "cr.mm"
include "wcel.mm"
include "4re.mm"
include "minveclem4c.mm"
include "resqcld.mm"
include "remulcl.mm"
include "sylancr.mm"
include "cme.mm"
include "cmt.mm"
include "cngp.mm"
include "ccph.mm"
include "cphngp.mm"
include "syl.mm"
include "ngpms.mm"
include "msmet.mm"
include "clss.mm"
include "wss.mm"
include "eqid.mm"
include "lssss.mm"
include "sseldd.mm"
include "metcl.mm"
include "syl3anc.mm"
include "readdcld.mm"
include "clmod.mm"
include "cphlmod.mm"
include "csca.mm"
include "cbs.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "cclm.mm"
include "cphclm.mm"
include "clmzss.mm"
include "2z.mm"
include "a1i.mm"
include "2ne0.mm"
include "cphreccl.mm"
include "lssvacl.mm"
include "syl22anc.mm"
include "lssvscl.mm"
include "lmodvsubcl.mm"
include "nmcl.mm"
include "syl2anc.mm"
include "clt.mm"
include "cinf.mm"
include "cv.mm"
include "wral.mm"
include "c0.mm"
include "minveclem1.mm"
include "simp3d.mm"
include "wrex.mm"
include "wb.mm"
include "simp1d.mm"
include "simp2d.mm"
include "0re.mm"
include "wceq.mm"
include "breq1.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "infregelb.mm"
include "syl31anc.mm"
include "mpbird.mm"
include "syl6breqr.mm"
include "cmpt.mm"
include "crn.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "sylancl.mm"
include "fvex.mm"
include "elrnmpti.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "infrelb.mm"
include "syl5eqbr.mm"
include "le2sq2.mm"
include "wa.mm"
include "4pos.mm"
include "pm3.2i.mm"
include "lemul2.mm"
include "mp3an3.mm"
include "mpbid.mm"
include "leadd1dd.mm"
include "le2addd.mm"
include "recnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "2re.mm"
include "2pos.mm"
include "nmpar.mm"
include "cc.mm"
include "2cn.mm"
include "sqmul.mm"
include "sq2.mm"
include "oveq1i.mm"
include "syl6eq.mm"
include "cabs.mm"
include "cphnmvs.mm"
include "0le2.mm"
include "absid.mm"
include "mp2an.mm"
include "lmodsubdi.mm"
include "cmg.mm"
include "mulg2.mm"
include "clmmulg.mm"
include "eqtr3d.mm"
include "lmodvacl.mm"
include "clmvs1.mm"
include "recidi.mm"
include "clmvsass.mm"
include "syl13anc.mm"
include "syl5eqr.mm"
include "oveq12d.mm"
include "cabl.mm"
include "lmodabl.mm"
include "ablsub4.mm"
include "syl122anc.mm"
include "3eqtr2d.mm"
include "oveq1d.mm"
include "cds.mm"
include "ngpdsr.mm"
include "cxp.mm"
include "cres.mm"
include "oveqi.mm"
include "ovresd.mm"
include "syl5eq.mm"
include "ablnnncan1.mm"
include "3eqtr4d.mm"
include "ngpds.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "2t2e4.mm"
include "2cnd.mm"
include "mulassd.mm"
include "3brtr4d.mm"
include "letrd.mm"
include "4cn.mm"
include "adddid.mm"
include "breqtrd.mm"
include "leadd2d.mm"

theorem minveclem2
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cJ: class J
  let cK: class K
  let cL: class L
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vw: setvar w
  let vx: setvar x
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cP: class P
  let cF: class F
  let cT: class T
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
  assume minveclem2.1: |- ( ph -> B e. RR )
  assume minveclem2.2: |- ( ph -> 0 <_ B )
  assume minveclem2.3: |- ( ph -> K e. Y )
  assume minveclem2.4: |- ( ph -> L e. Y )
  assume minveclem2.5: |- ( ph -> ( ( A D K ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) )
  assume minveclem2.6: |- ( ph -> ( ( A D L ) ^ 2 ) <_ ( ( S ^ 2 ) + B ) )

  disjoint .- y
  disjoint A y
  disjoint J y
  disjoint K y
  disjoint N y
  disjoint ph y
  disjoint R y
  disjoint U y
  disjoint X y
  disjoint Y y
  disjoint D y
  disjoint S y
  disjoint L y
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
  disjoint r y
  disjoint r z
  disjoint A r
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
  disjoint J r
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
  disjoint F y
  disjoint N j
  disjoint N w
  disjoint N x
  disjoint ph r
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
  disjoint X r
  disjoint X w
  disjoint X x
  disjoint Y j
  disjoint Y r
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y z
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S z
  disjoint T r
  disjoint T y
  assert |- ( ph -> ( ( K D L ) ^ 2 ) <_ ( 4 x. B ) )

  proof
    wph
    cK
    cL
    cD
    co
    #
    c2
    cexp
    co
    #
    c4
    cB
    cmul
    co
    #
    cle
    wbr
    c4
    cS
    c2
    cexp
    co
    #
    cmul
    co
    #
    @1
    caddc
    co
    #
    @4
    @2
    caddc
    co
    #
    cle
    wbr
    wph
    @5
    c4
    @3
    cB
    caddc
    co
    #
    cmul
    co
    #
    @6
    cle
    wph
    @5
    c4
    cA
    c1
    c2
    cdiv
    co
    #
    cK
    cL
    cU
    cplusg
    cfv
    #
    co
    #
    cU
    cvsca
    cfv
    #
    co
    #
    c.mi
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmul
    co
    #
    @1
    caddc
    co
    #
    @8
    wph
    @4
    @1
    wph
    c4
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    4re
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
    #
    resqcld
    #
    c4
    @3
    remulcl
    sylancr
    #
    wph
    @0
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    cK
    cX
    wcel
    #
    cL
    cX
    wcel
    #
    @0
    cr
    wcel
    wph
    cU
    cmt
    wcel
    #
    @24
    wph
    cU
    cngp
    wcel
    #
    @27
    wph
    cU
    ccph
    wcel
    #
    @28
    minvec.u
    cU
    cphngp
    syl
    #
    cU
    ngpms
    syl
    cD
    cU
    cX
    minvec.x
    minvec.d
    msmet
    syl
    #
    wph
    cY
    cX
    cK
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
    minvec.y
    @32
    cY
    cX
    cU
    minvec.x
    @32
    eqid
    #
    lssss
    syl
    #
    minveclem2.3
    sseldd
    #
    wph
    cY
    cX
    cL
    @35
    minveclem2.4
    sseldd
    #
    cK
    cL
    cD
    cX
    metcl
    syl3anc
    resqcld
    #
    readdcld
    wph
    @17
    @1
    wph
    @19
    @16
    cr
    wcel
    #
    @17
    cr
    wcel
    4re
    wph
    @15
    wph
    @28
    @14
    cX
    wcel
    #
    @15
    cr
    wcel
    #
    @30
    wph
    cU
    clmod
    wcel
    #
    cA
    cX
    wcel
    #
    @13
    cX
    wcel
    @40
    wph
    @29
    @42
    minvec.u
    cU
    cphlmod
    syl
    #
    minvec.a
    wph
    cY
    cX
    @13
    @35
    wph
    @42
    @33
    @9
    cU
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @11
    cY
    wcel
    #
    @13
    cY
    wcel
    #
    @44
    minvec.y
    wph
    @29
    c2
    @46
    wcel
    #
    c2
    cc0
    wne
    #
    @47
    minvec.u
    wph
    cz
    @46
    c2
    wph
    cU
    cclm
    wcel
    #
    cz
    @46
    wss
    wph
    @29
    @52
    minvec.u
    cU
    cphclm
    syl
    #
    @45
    @46
    cU
    @45
    eqid
    #
    @46
    eqid
    #
    clmzss
    syl
    c2
    cz
    wcel
    #
    wph
    2z
    a1i
    #
    sseldd
    #
    @51
    wph
    2ne0
    a1i
    c2
    @45
    @46
    cU
    @54
    @55
    cphreccl
    syl3anc
    #
    wph
    @42
    @33
    cK
    cY
    wcel
    cL
    cY
    wcel
    @48
    @44
    minvec.y
    minveclem2.3
    minveclem2.4
    @10
    @32
    cY
    cU
    cK
    cL
    @10
    eqid
    #
    @34
    lssvacl
    syl22anc
    @46
    @32
    @12
    cY
    @45
    cU
    @9
    @11
    @54
    @12
    eqid
    #
    @55
    @34
    lssvscl
    syl22anc
    #
    sseldd
    #
    c.mi
    cX
    cU
    cA
    @13
    minvec.x
    minvec.m
    lmodvsubcl
    syl3anc
    #
    @14
    cU
    cN
    cX
    minvec.x
    minvec.n
    nmcl
    syl2anc
    #
    resqcld
    #
    c4
    @16
    remulcl
    sylancr
    #
    @38
    readdcld
    wph
    @19
    @7
    cr
    wcel
    #
    @8
    cr
    wcel
    4re
    wph
    @3
    cB
    @22
    minveclem2.1
    readdcld
    #
    c4
    @7
    remulcl
    sylancr
    wph
    @4
    @17
    @1
    @23
    @67
    @38
    wph
    @3
    @16
    cle
    wbr
    #
    @4
    @17
    cle
    wbr
    #
    wph
    cS
    cr
    wcel
    cc0
    cS
    cle
    wbr
    @41
    cS
    @15
    cle
    wbr
    @70
    @21
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
    @72
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
    @76
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
    @77
    @78
    vx
    cv
    #
    @74
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
    @73
    @76
    wb
    wph
    @77
    @78
    @76
    @79
    simp1d
    #
    wph
    @77
    @78
    @76
    @79
    simp2d
    wph
    @85
    @76
    @84
    0re
    @80
    @83
    @76
    vx
    cc0
    cr
    @81
    cc0
    wceq
    @82
    @75
    vw
    cR
    @81
    cc0
    @74
    cle
    breq1
    ralbidv
    rspcev
    sylancr
    #
    @85
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
    @65
    wph
    cS
    @72
    @15
    cle
    minvec.s
    wph
    @77
    @84
    @15
    cR
    wcel
    @72
    @15
    cle
    wbr
    @86
    @87
    wph
    @15
    vy
    cY
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
    cmpt
    #
    crn
    #
    cR
    wph
    @15
    @90
    wceq
    #
    vy
    cY
    wrex
    #
    @15
    @92
    wcel
    wph
    @49
    @15
    @15
    wceq
    #
    @94
    @62
    @15
    eqid
    @93
    @95
    vy
    @13
    cY
    @88
    @13
    wceq
    #
    @90
    @15
    @15
    @96
    @89
    @14
    cN
    @88
    @13
    cA
    c.mi
    oveq2
    fveq2d
    eqeq2d
    rspcev
    sylancl
    vy
    cY
    @90
    @15
    @91
    @91
    eqid
    @89
    cN
    fvex
    elrnmpti
    sylibr
    minvec.r
    syl6eleqr
    vx
    vw
    @15
    cR
    infrelb
    syl3anc
    syl5eqbr
    cS
    @15
    le2sq2
    syl22anc
    wph
    @20
    @39
    @70
    @71
    wb
    #
    @22
    @66
    @20
    @39
    @19
    cc0
    c4
    clt
    wbr
    #
    wa
    @97
    @19
    @98
    4re
    4pos
    pm3.2i
    @3
    @16
    c4
    lemul2
    mp3an3
    syl2anc
    mpbid
    leadd1dd
    wph
    c2
    cA
    cK
    cD
    co
    #
    c2
    cexp
    co
    #
    cA
    cL
    cD
    co
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    c2
    c2
    @7
    cmul
    co
    #
    cmul
    co
    #
    @18
    @8
    cle
    wph
    @103
    @105
    cle
    wbr
    #
    @104
    @106
    cle
    wbr
    #
    wph
    @103
    @7
    @7
    caddc
    co
    @105
    cle
    wph
    @100
    @102
    @7
    @7
    wph
    @99
    wph
    @24
    @43
    @25
    @99
    cr
    wcel
    @31
    minvec.a
    @36
    cA
    cK
    cD
    cX
    metcl
    syl3anc
    resqcld
    #
    wph
    @101
    wph
    @24
    @43
    @26
    @101
    cr
    wcel
    @31
    minvec.a
    @37
    cA
    cL
    cD
    cX
    metcl
    syl3anc
    resqcld
    #
    @69
    @69
    minveclem2.5
    minveclem2.6
    le2addd
    wph
    @7
    wph
    @7
    @69
    recnd
    #
    2timesd
    breqtrrd
    wph
    @103
    cr
    wcel
    #
    @105
    cr
    wcel
    #
    @107
    @108
    wb
    #
    wph
    @100
    @102
    @109
    @110
    readdcld
    wph
    c2
    cr
    wcel
    #
    @68
    @113
    2re
    @69
    c2
    @7
    remulcl
    sylancr
    @112
    @113
    @115
    cc0
    c2
    clt
    wbr
    #
    wa
    @114
    @115
    @116
    2re
    2pos
    pm3.2i
    @103
    @105
    c2
    lemul2
    mp3an3
    syl2anc
    mpbid
    wph
    cA
    cK
    c.mi
    co
    #
    cA
    cL
    c.mi
    co
    #
    @10
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    @117
    @118
    c.mi
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    @117
    cN
    cfv
    #
    c2
    cexp
    co
    #
    @118
    cN
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    cmul
    co
    #
    @18
    @104
    wph
    @29
    @117
    cX
    wcel
    #
    @118
    cX
    wcel
    #
    @125
    @131
    wceq
    minvec.u
    wph
    @42
    @43
    @25
    @132
    @44
    minvec.a
    @36
    c.mi
    cX
    cU
    cA
    cK
    minvec.x
    minvec.m
    lmodvsubcl
    syl3anc
    wph
    @42
    @43
    @26
    @133
    @44
    minvec.a
    @37
    c.mi
    cX
    cU
    cA
    cL
    minvec.x
    minvec.m
    lmodvsubcl
    syl3anc
    @117
    @118
    @10
    c.mi
    cN
    cX
    cU
    minvec.x
    @60
    minvec.m
    minvec.n
    nmpar
    syl3anc
    wph
    @17
    @121
    @1
    @124
    caddc
    wph
    c2
    @15
    cmul
    co
    #
    c2
    cexp
    co
    #
    @17
    @121
    wph
    @135
    c2
    c2
    cexp
    co
    #
    @16
    cmul
    co
    #
    @17
    wph
    c2
    cc
    wcel
    @15
    cc
    wcel
    @135
    @137
    wceq
    2cn
    wph
    @15
    @65
    recnd
    c2
    @15
    sqmul
    sylancr
    @136
    c4
    @16
    cmul
    sq2
    oveq1i
    syl6eq
    wph
    @134
    @120
    c2
    cexp
    wph
    c2
    @14
    @12
    co
    #
    cN
    cfv
    #
    @134
    @120
    wph
    @139
    c2
    cabs
    cfv
    #
    @15
    cmul
    co
    #
    @134
    wph
    @29
    @50
    @40
    @139
    @141
    wceq
    minvec.u
    @58
    @64
    @12
    @45
    @46
    cN
    cX
    cU
    c2
    @14
    minvec.x
    minvec.n
    @61
    @54
    @55
    cphnmvs
    syl3anc
    @140
    c2
    @15
    cmul
    @115
    cc0
    c2
    cle
    wbr
    @140
    c2
    wceq
    2re
    0le2
    c2
    absid
    mp2an
    oveq1i
    syl6eq
    wph
    @138
    @119
    cN
    wph
    @138
    c2
    cA
    @12
    co
    #
    c2
    @13
    @12
    co
    #
    c.mi
    co
    cA
    cA
    @10
    co
    #
    @11
    c.mi
    co
    #
    @119
    wph
    c2
    @12
    @45
    @46
    c.mi
    cX
    cU
    cA
    @13
    minvec.x
    @61
    @54
    @55
    minvec.m
    @44
    @58
    minvec.a
    @63
    lmodsubdi
    wph
    @144
    @142
    @11
    @143
    c.mi
    wph
    c2
    cA
    cU
    cmg
    cfv
    #
    co
    #
    @144
    @142
    wph
    @43
    @147
    @144
    wceq
    minvec.a
    cX
    @10
    @146
    cU
    cA
    minvec.x
    @146
    eqid
    #
    @60
    mulg2
    syl
    wph
    @52
    @56
    @43
    @147
    @142
    wceq
    @53
    @57
    minvec.a
    c2
    cA
    @146
    @12
    cX
    cU
    minvec.x
    @148
    @61
    clmmulg
    syl3anc
    eqtr3d
    wph
    c1
    @11
    @12
    co
    #
    @11
    @143
    wph
    @52
    @11
    cX
    wcel
    #
    @149
    @11
    wceq
    @53
    wph
    @42
    @25
    @26
    @150
    @44
    @36
    @37
    @10
    cX
    cU
    cK
    cL
    minvec.x
    @60
    lmodvacl
    syl3anc
    #
    @12
    cX
    cU
    @11
    minvec.x
    @61
    clmvs1
    syl2anc
    wph
    @149
    c2
    @9
    cmul
    co
    #
    @11
    @12
    co
    #
    @143
    @152
    c1
    @11
    @12
    c2
    2cn
    2ne0
    recidi
    oveq1i
    wph
    @52
    @50
    @47
    @150
    @153
    @143
    wceq
    @53
    @58
    @59
    @151
    c2
    @9
    @12
    @45
    @46
    cX
    cU
    @11
    minvec.x
    @54
    @61
    @55
    clmvsass
    syl13anc
    syl5eqr
    eqtr3d
    oveq12d
    wph
    cU
    cabl
    wcel
    #
    @43
    @43
    @25
    @26
    @145
    @119
    wceq
    wph
    @42
    @154
    @44
    cU
    lmodabl
    syl
    #
    minvec.a
    minvec.a
    @36
    @37
    cX
    @10
    cU
    c.mi
    cL
    cA
    cA
    cK
    minvec.x
    @60
    minvec.m
    ablsub4
    syl122anc
    3eqtr2d
    fveq2d
    eqtr3d
    oveq1d
    eqtr3d
    wph
    @0
    @123
    c2
    cexp
    wph
    cK
    cL
    cU
    cds
    cfv
    #
    co
    #
    cL
    cK
    c.mi
    co
    #
    cN
    cfv
    #
    @0
    @123
    wph
    @28
    @25
    @26
    @157
    @159
    wceq
    @30
    @36
    @37
    cK
    cL
    @156
    cU
    c.mi
    cN
    cX
    minvec.n
    minvec.x
    minvec.m
    @156
    eqid
    #
    ngpdsr
    syl3anc
    wph
    @0
    cK
    cL
    @156
    cX
    cX
    cxp
    cres
    #
    co
    @157
    cD
    @161
    cK
    cL
    minvec.d
    oveqi
    wph
    cK
    cL
    @156
    cX
    @36
    @37
    ovresd
    syl5eq
    wph
    @122
    @158
    cN
    wph
    cX
    cU
    c.mi
    cA
    cK
    cL
    minvec.x
    minvec.m
    @155
    minvec.a
    @36
    @37
    ablnnncan1
    fveq2d
    3eqtr4d
    oveq1d
    oveq12d
    wph
    @103
    @130
    c2
    cmul
    wph
    @100
    @127
    @102
    @129
    caddc
    wph
    @99
    @126
    c2
    cexp
    wph
    @99
    cA
    cK
    @156
    co
    #
    @126
    wph
    @99
    cA
    cK
    @161
    co
    @162
    cD
    @161
    cA
    cK
    minvec.d
    oveqi
    wph
    cA
    cK
    @156
    cX
    minvec.a
    @36
    ovresd
    syl5eq
    wph
    @28
    @43
    @25
    @162
    @126
    wceq
    @30
    minvec.a
    @36
    cA
    cK
    @156
    cU
    c.mi
    cN
    cX
    minvec.n
    minvec.x
    minvec.m
    @160
    ngpds
    syl3anc
    eqtrd
    oveq1d
    wph
    @101
    @128
    c2
    cexp
    wph
    @101
    cA
    cL
    @156
    co
    #
    @128
    wph
    @101
    cA
    cL
    @161
    co
    @163
    cD
    @161
    cA
    cL
    minvec.d
    oveqi
    wph
    cA
    cL
    @156
    cX
    minvec.a
    @37
    ovresd
    syl5eq
    wph
    @28
    @43
    @26
    @163
    @128
    wceq
    @30
    minvec.a
    @37
    cA
    cL
    @156
    cU
    c.mi
    cN
    cX
    minvec.n
    minvec.x
    minvec.m
    @160
    ngpds
    syl3anc
    eqtrd
    oveq1d
    oveq12d
    oveq2d
    3eqtr4d
    wph
    @8
    c2
    c2
    cmul
    co
    #
    @7
    cmul
    co
    @106
    @164
    c4
    @7
    cmul
    2t2e4
    oveq1i
    wph
    c2
    c2
    @7
    wph
    2cnd
    #
    @165
    @111
    mulassd
    syl5eqr
    3brtr4d
    letrd
    wph
    c4
    @3
    cB
    c4
    cc
    wcel
    wph
    4cn
    a1i
    wph
    @3
    @22
    recnd
    wph
    cB
    minveclem2.1
    recnd
    adddid
    breqtrd
    wph
    @1
    @2
    @4
    @38
    wph
    @19
    cB
    cr
    wcel
    @2
    cr
    wcel
    4re
    minveclem2.1
    c4
    cB
    remulcl
    sylancr
    @23
    leadd2d
    mpbird
end
