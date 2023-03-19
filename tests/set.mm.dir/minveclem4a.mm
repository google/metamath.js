include "cfg.mm"
include "co.mm"
include "cflim.mm"
include "cuni.mm"
include "cin.mm"
include "csn.mm"
include "ovex.mm"
include "uniex.mm"
include "snid.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "cfv.mm"
include "crest.mm"
include "cxme.mm"
include "wcel.mm"
include "ccph.mm"
include "cngp.mm"
include "cphngp.mm"
include "ngpxms.mm"
include "3syl.mm"
include "xmstopn.mm"
include "syl.mm"
include "oveq1d.mm"
include "cxmt.mm"
include "wss.mm"
include "xmsxmet.mm"
include "clss.mm"
include "eqid.mm"
include "lssss.mm"
include "metrest.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "cfil.mm"
include "cvv.mm"
include "cfbas.mm"
include "minveclem3b.mm"
include "fgcl.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "trfg.mm"
include "syl3anc.mm"
include "fgabs.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "ctopon.mm"
include "ctps.mm"
include "xmstps.mm"
include "istps.mm"
include "sylib.mm"
include "cpw.mm"
include "fbsspw.mm"
include "sspwb.mm"
include "sstrd.mm"
include "fbasweak.mm"
include "filfbas.mm"
include "ssfg.mm"
include "sseqtrd.mm"
include "filtop.mm"
include "sseldd.mm"
include "flimrest.mm"
include "eqtrd.mm"
include "cms.mm"
include "ccfil.mm"
include "wne.mm"
include "minveclem3a.mm"
include "minveclem3.mm"
include "cmetcvg.mm"
include "eqnetrrd.mm"
include "neneqd.mm"
include "wo.mm"
include "inss1.mm"
include "c1o.mm"
include "cen.mm"
include "wbr.mm"
include "cv.mm"
include "weu.mm"
include "wmo.mm"
include "cha.mm"
include "methaus.mm"
include "eqeltrd.mm"
include "hausflimi.mm"
include "wb.mm"
include "ssn0.mm"
include "sylancr.mm"
include "n0moeu.mm"
include "mpbid.mm"
include "euen1b.mm"
include "sylibr.mm"
include "en1b.mm"
include "syl5sseq.mm"
include "sssn.mm"
include "ord.mm"
include "mpd.mm"
include "syl5eleqr.mm"
include "syl5eqel.mm"

theorem minveclem4a
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cP: class P
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
  assume minvec.p: |- P = U. ( J fLim ( X filGen F ) )

  disjoint .- y
  disjoint r y
  disjoint A r
  disjoint A y
  disjoint J r
  disjoint J y
  disjoint P y
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
  assert |- ( ph -> P e. ( ( J fLim ( X filGen F ) ) i^i Y ) )

  proof
    wph
    cP
    cJ
    cX
    cF
    cfg
    co
    #
    cflim
    co
    #
    cuni
    #
    @1
    cY
    cin
    #
    minvec.p
    wph
    @2
    @2
    csn
    #
    @3
    @2
    @1
    cJ
    @0
    cflim
    ovex
    uniex
    snid
    wph
    @3
    c0
    wceq
    #
    wn
    @3
    @4
    wceq
    #
    wph
    @3
    c0
    wph
    cD
    cY
    cY
    cxp
    cres
    #
    cmopn
    cfv
    #
    cY
    cF
    cfg
    co
    #
    cflim
    co
    #
    @3
    c0
    wph
    @10
    cJ
    cY
    crest
    co
    #
    @0
    cY
    crest
    co
    #
    cflim
    co
    #
    @3
    wph
    @8
    @11
    @9
    @12
    cflim
    wph
    @11
    cD
    cmopn
    cfv
    #
    cY
    crest
    co
    #
    @8
    wph
    cJ
    @14
    cY
    crest
    wph
    cU
    cxme
    wcel
    #
    cJ
    @14
    wceq
    wph
    cU
    ccph
    wcel
    cU
    cngp
    wcel
    @16
    minvec.u
    cU
    cphngp
    cU
    ngpxms
    3syl
    #
    cD
    cJ
    cU
    cX
    minvec.j
    minvec.x
    minvec.d
    xmstopn
    #
    syl
    oveq1d
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cY
    cX
    wss
    #
    @15
    @8
    wceq
    wph
    @16
    @19
    @17
    cD
    cU
    cX
    minvec.x
    minvec.d
    xmsxmet
    #
    syl
    wph
    cY
    cU
    clss
    cfv
    #
    wcel
    @20
    minvec.y
    @22
    cY
    cX
    cU
    minvec.x
    @22
    eqid
    lssss
    syl
    #
    cD
    @7
    @14
    @8
    cX
    cY
    @7
    eqid
    @14
    eqid
    #
    @8
    eqid
    #
    metrest
    syl2anc
    eqtr2d
    wph
    cX
    @9
    cfg
    co
    #
    cY
    crest
    co
    #
    @9
    @12
    wph
    @9
    cY
    cfil
    cfv
    wcel
    #
    @20
    cX
    cvv
    wcel
    #
    @27
    @9
    wceq
    wph
    cF
    cY
    cfbas
    cfv
    #
    wcel
    #
    @28
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
    cF
    cY
    fgcl
    #
    syl
    #
    @23
    @29
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
    #
    cY
    @9
    cvv
    cX
    trfg
    syl3anc
    wph
    @26
    @0
    cY
    crest
    wph
    @31
    @20
    @26
    @0
    wceq
    @32
    @23
    cF
    cX
    cY
    fgabs
    syl2anc
    #
    oveq1d
    eqtr3d
    oveq12d
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @0
    cX
    cfil
    cfv
    wcel
    #
    cY
    @0
    wcel
    @13
    @3
    wceq
    wph
    cU
    ctps
    wcel
    #
    @37
    wph
    @16
    @39
    @17
    cU
    xmstps
    syl
    cX
    cJ
    cU
    minvec.x
    minvec.j
    istps
    sylib
    wph
    cF
    cX
    cfbas
    cfv
    #
    wcel
    #
    @38
    wph
    @31
    cF
    cX
    cpw
    #
    wss
    @29
    @41
    @32
    wph
    cF
    cY
    cpw
    #
    @42
    wph
    @31
    cF
    @43
    wss
    @32
    cY
    cF
    fbsspw
    syl
    wph
    @20
    @43
    @42
    wss
    @23
    cY
    cX
    sspwb
    sylib
    #
    sstrd
    @35
    cF
    cvv
    cY
    cX
    fbasweak
    syl3anc
    cF
    cX
    fgcl
    syl
    wph
    @9
    @0
    cY
    wph
    @9
    @26
    @0
    wph
    @9
    @40
    wcel
    #
    @9
    @26
    wss
    wph
    @9
    @30
    wcel
    #
    @9
    @42
    wss
    @29
    @45
    wph
    @31
    @28
    @46
    @32
    @33
    @9
    cY
    filfbas
    3syl
    #
    wph
    @9
    @43
    @42
    wph
    @46
    @9
    @43
    wss
    @47
    cY
    @9
    fbsspw
    syl
    @44
    sstrd
    @35
    @9
    cvv
    cY
    cX
    fbasweak
    syl3anc
    @9
    cX
    ssfg
    syl
    @36
    sseqtrd
    wph
    @28
    cY
    @9
    wcel
    @34
    @9
    cY
    filtop
    syl
    sseldd
    @0
    cJ
    cX
    cY
    flimrest
    syl3anc
    eqtrd
    wph
    @7
    cY
    cms
    cfv
    wcel
    @9
    @7
    ccfil
    cfv
    wcel
    @10
    c0
    wne
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
    minveclem3
    @7
    @9
    @8
    cY
    @25
    cmetcvg
    syl2anc
    eqnetrrd
    #
    neneqd
    wph
    @5
    @6
    wph
    @3
    @4
    wss
    @5
    @6
    wo
    wph
    @1
    @3
    @4
    @1
    cY
    inss1
    #
    wph
    @1
    c1o
    cen
    wbr
    #
    @1
    @4
    wceq
    wph
    vx
    cv
    @1
    wcel
    #
    vx
    weu
    #
    @50
    wph
    @51
    vx
    wmo
    #
    @52
    wph
    @16
    cJ
    cha
    wcel
    @53
    @17
    @16
    cJ
    @14
    cha
    @18
    @16
    @19
    @14
    cha
    wcel
    @21
    cD
    @14
    cX
    @24
    methaus
    syl
    eqeltrd
    vx
    @0
    cJ
    hausflimi
    3syl
    wph
    @1
    c0
    wne
    #
    @53
    @52
    wb
    wph
    @3
    @1
    wss
    @3
    c0
    wne
    @54
    @49
    @48
    @3
    @1
    ssn0
    sylancr
    vx
    @1
    n0moeu
    syl
    mpbid
    vx
    @1
    euen1b
    sylibr
    @1
    en1b
    sylib
    syl5sseq
    @3
    @2
    sssn
    sylib
    ord
    mpd
    syl5eleqr
    syl5eqel
end
