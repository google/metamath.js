include "cfg.mm"
include "co.mm"
include "cxp.mm"
include "cres.mm"
include "ccfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "c4.mm"
include "caddc.mm"
include "cle.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cvv.mm"
include "cz.mm"
include "simpr.mm"
include "2z.mm"
include "rpexpcl.mm"
include "sylancl.mm"
include "rphalfcld.mm"
include "cn.mm"
include "4nn.mm"
include "nnrp.mm"
include "ax-mp.mm"
include "rpdivcl.mm"
include "clss.mm"
include "adantr.mm"
include "rabexg.mm"
include "syl.mm"
include "eqid.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "elrnmpt1s.mm"
include "syl2anc.mm"
include "syl6eleqr.mm"
include "weq.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "elrab.mm"
include "anbi12i.mm"
include "simprll.mm"
include "simprrl.mm"
include "ovresd.mm"
include "cme.mm"
include "cr.mm"
include "ccph.mm"
include "cngp.mm"
include "cmt.mm"
include "cphngp.mm"
include "ngpms.mm"
include "msmet.mm"
include "4syl.mm"
include "ad2antrr.mm"
include "wss.mm"
include "lssss.mm"
include "sseldd.mm"
include "metcl.mm"
include "syl3anc.mm"
include "resqcld.mm"
include "rpred.mm"
include "cmul.mm"
include "cress.mm"
include "ccms.mm"
include "rpge0d.mm"
include "simprlr.mm"
include "simprrr.mm"
include "minveclem2.mm"
include "rpcnd.mm"
include "cc.mm"
include "4cn.mm"
include "a1i.mm"
include "cc0.mm"
include "wne.mm"
include "4ne0.mm"
include "divcan2d.mm"
include "breqtrd.mm"
include "rphalflt.mm"
include "lelttrd.mm"
include "rpre.mm"
include "ad2antlr.mm"
include "metge0.mm"
include "rpge0.mm"
include "lt2sqd.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "sylan2b.mm"
include "ralrimivva.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "cxmt.mm"
include "cfbas.mm"
include "wb.mm"
include "cms.mm"
include "minveclem3a.mm"
include "cmetmet.mm"
include "metxmet.mm"
include "3syl.mm"
include "minveclem3b.mm"
include "fgcfil.mm"

theorem minveclem3
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
  assert |- ( ph -> ( Y filGen F ) e. ( CauFil ` ( D |` ( Y X. Y ) ) ) )

  proof
    wph
    cY
    cF
    cfg
    co
    cD
    cY
    cY
    cxp
    cres
    #
    ccfil
    cfv
    wcel
    #
    vu
    cv
    #
    vv
    cv
    #
    @0
    co
    #
    vs
    cv
    #
    clt
    wbr
    #
    vv
    vw
    cv
    #
    wral
    #
    vu
    @7
    wral
    #
    vw
    cF
    wrex
    #
    vs
    crp
    wral
    #
    wph
    @10
    vs
    crp
    wph
    @5
    crp
    wcel
    #
    wa
    #
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
    @5
    c2
    cexp
    co
    #
    c2
    cdiv
    co
    #
    c4
    cdiv
    co
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
    cF
    wcel
    @6
    vv
    @23
    wral
    #
    vu
    @23
    wral
    #
    @10
    @13
    @23
    vr
    crp
    @16
    @17
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
    @13
    @20
    crp
    wcel
    #
    @23
    cvv
    wcel
    #
    @23
    @31
    wcel
    @13
    @19
    crp
    wcel
    #
    c4
    crp
    wcel
    #
    @32
    @13
    @18
    @13
    @12
    c2
    cz
    wcel
    @18
    crp
    wcel
    #
    wph
    @12
    simpr
    2z
    @5
    c2
    rpexpcl
    sylancl
    #
    rphalfcld
    #
    c4
    cn
    wcel
    @35
    4nn
    c4
    nnrp
    ax-mp
    @19
    c4
    rpdivcl
    sylancl
    #
    @13
    cY
    cU
    clss
    cfv
    #
    wcel
    #
    @33
    wph
    @41
    @12
    minvec.y
    adantr
    @22
    vy
    cY
    @40
    rabexg
    syl
    vr
    crp
    @29
    @23
    @20
    @30
    cvv
    @30
    eqid
    @26
    @20
    wceq
    #
    @28
    @22
    vy
    cY
    @42
    @27
    @21
    @16
    cle
    @26
    @20
    @17
    caddc
    oveq2
    breq2d
    rabbidv
    elrnmpt1s
    syl2anc
    minvec.f
    syl6eleqr
    @13
    @6
    vu
    vv
    @23
    @23
    @2
    @23
    wcel
    #
    @3
    @23
    wcel
    #
    wa
    @13
    @2
    cY
    wcel
    #
    cA
    @2
    cD
    co
    #
    c2
    cexp
    co
    #
    @21
    cle
    wbr
    #
    wa
    #
    @3
    cY
    wcel
    #
    cA
    @3
    cD
    co
    #
    c2
    cexp
    co
    #
    @21
    cle
    wbr
    #
    wa
    #
    wa
    #
    @6
    @43
    @49
    @44
    @54
    @22
    @48
    vy
    @2
    cY
    vy
    vu
    weq
    #
    @16
    @47
    @21
    cle
    @56
    @15
    @46
    c2
    cexp
    @14
    @2
    cA
    cD
    oveq2
    oveq1d
    breq1d
    elrab
    @22
    @53
    vy
    @3
    cY
    vy
    vv
    weq
    #
    @16
    @52
    @21
    cle
    @57
    @15
    @51
    c2
    cexp
    @14
    @3
    cA
    cD
    oveq2
    oveq1d
    breq1d
    elrab
    anbi12i
    @13
    @55
    wa
    #
    @4
    @2
    @3
    cD
    co
    #
    @5
    clt
    @58
    @2
    @3
    cD
    cY
    @13
    @45
    @48
    @54
    simprll
    #
    @13
    @49
    @50
    @53
    simprrl
    #
    ovresd
    @58
    @59
    @5
    clt
    wbr
    @59
    c2
    cexp
    co
    #
    @18
    clt
    wbr
    @58
    @62
    @19
    @18
    @58
    @59
    @58
    cD
    cX
    cme
    cfv
    wcel
    #
    @2
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    @59
    cr
    wcel
    wph
    @63
    @12
    @55
    wph
    cU
    ccph
    wcel
    #
    cU
    cngp
    wcel
    cU
    cmt
    wcel
    @63
    minvec.u
    cU
    cphngp
    cU
    ngpms
    cD
    cU
    cX
    minvec.x
    minvec.d
    msmet
    4syl
    ad2antrr
    #
    @58
    cY
    cX
    @2
    wph
    cY
    cX
    wss
    #
    @12
    @55
    wph
    @41
    @68
    minvec.y
    @40
    cY
    cX
    cU
    minvec.x
    @40
    eqid
    lssss
    syl
    ad2antrr
    #
    @60
    sseldd
    #
    @58
    cY
    cX
    @3
    @69
    @61
    sseldd
    #
    @2
    @3
    cD
    cX
    metcl
    syl3anc
    #
    resqcld
    @58
    @19
    @13
    @34
    @55
    @38
    adantr
    #
    rpred
    @58
    @18
    @13
    @36
    @55
    @37
    adantr
    #
    rpred
    @58
    @62
    c4
    @20
    cmul
    co
    @19
    cle
    @58
    vy
    cA
    @20
    cD
    cR
    cS
    cU
    cJ
    @2
    @3
    c.mi
    cN
    cX
    cY
    minvec.x
    minvec.m
    minvec.n
    wph
    @66
    @12
    @55
    minvec.u
    ad2antrr
    wph
    @41
    @12
    @55
    minvec.y
    ad2antrr
    wph
    cU
    cY
    cress
    co
    ccms
    wcel
    @12
    @55
    minvec.w
    ad2antrr
    wph
    cA
    cX
    wcel
    @12
    @55
    minvec.a
    ad2antrr
    minvec.j
    minvec.r
    minvec.s
    minvec.d
    @58
    @20
    @13
    @32
    @55
    @39
    adantr
    #
    rpred
    @58
    @20
    @75
    rpge0d
    @60
    @61
    @13
    @45
    @48
    @54
    simprlr
    @13
    @49
    @50
    @53
    simprrr
    minveclem2
    @58
    @19
    c4
    @58
    @19
    @73
    rpcnd
    c4
    cc
    wcel
    @58
    4cn
    a1i
    c4
    cc0
    wne
    @58
    4ne0
    a1i
    divcan2d
    breqtrd
    @58
    @36
    @19
    @18
    clt
    wbr
    @74
    @18
    rphalflt
    syl
    lelttrd
    @58
    @59
    @5
    @72
    @12
    @5
    cr
    wcel
    wph
    @55
    @5
    rpre
    ad2antlr
    @58
    @63
    @64
    @65
    cc0
    @59
    cle
    wbr
    @67
    @70
    @71
    @2
    @3
    cD
    cX
    metge0
    syl3anc
    @12
    cc0
    @5
    cle
    wbr
    wph
    @55
    @5
    rpge0
    ad2antlr
    lt2sqd
    mpbird
    eqbrtrd
    sylan2b
    ralrimivva
    @9
    @25
    vw
    @23
    cF
    @8
    @24
    vu
    @7
    @23
    @6
    vv
    @7
    @23
    raleq
    raleqbi1dv
    rspcev
    syl2anc
    ralrimiva
    wph
    @0
    cY
    cxmt
    cfv
    wcel
    #
    cF
    cY
    cfbas
    cfv
    wcel
    @1
    @11
    wb
    wph
    @0
    cY
    cms
    cfv
    wcel
    @0
    cY
    cme
    cfv
    wcel
    @76
    wph
    vy
    cA
    cD
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
    minvec.d
    minveclem3a
    @0
    cY
    cmetmet
    @0
    cY
    metxmet
    3syl
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
    vs
    vw
    vu
    vv
    cF
    @0
    cY
    fgcfil
    syl2anc
    mpbird
end
