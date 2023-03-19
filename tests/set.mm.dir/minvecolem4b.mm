include "clm.mm"
include "cfv.mm"
include "cnv.mm"
include "wcel.mm"
include "css.mm"
include "wss.mm"
include "ccphlo.mm"
include "phnv.mm"
include "syl.mm"
include "ccbn.mm"
include "cin.mm"
include "wa.mm"
include "elin.mm"
include "sylib.mm"
include "simpld.mm"
include "eqid.mm"
include "sspba.mm"
include "syl2anc.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "wfun.mm"
include "wbr.mm"
include "wceq.mm"
include "cha.mm"
include "cxmt.mm"
include "imsxmet.mm"
include "methaus.mm"
include "lmfun.mm"
include "minvecolem4a.mm"
include "crest.mm"
include "co.mm"
include "c1.mm"
include "cvv.mm"
include "cn.mm"
include "nnuz.mm"
include "cba.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ctop.mm"
include "mopntop.mm"
include "ctopon.mm"
include "xmetres2.mm"
include "mopntopon.mm"
include "lmcl.mm"
include "1zzd.mm"
include "lmss.mm"
include "metrest.mm"
include "fveq2d.mm"
include "breqd.mm"
include "bitrd.mm"
include "mpbird.mm"
include "funbrfv.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "sseldd.mm"

theorem minvecolem4b
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let vn: setvar n
  let cF: class F
  let cJ: class J
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vx: setvar x
  let vk: setvar k
  let vw: setvar w
  let cK: class K
  let cL: class L
  let vf: setvar f
  let cT: class T
  assume minveco.x: |- X = ( BaseSet ` U )
  assume minveco.m: |- M = ( -v ` U )
  assume minveco.n: |- N = ( normCV ` U )
  assume minveco.y: |- Y = ( BaseSet ` W )
  assume minveco.u: |- ( ph -> U e. CPreHilOLD )
  assume minveco.w: |- ( ph -> W e. ( ( SubSp ` U ) i^i CBan ) )
  assume minveco.a: |- ( ph -> A e. X )
  assume minveco.d: |- D = ( IndMet ` U )
  assume minveco.j: |- J = ( MetOpen ` D )
  assume minveco.r: |- R = ran ( y e. Y |-> ( N ` ( A M y ) ) )
  assume minveco.s: |- S = inf ( R , RR , < )
  assume minveco.f: |- ( ph -> F : NN --> Y )
  assume minveco.1: |- ( ( ph /\ n e. NN ) -> ( ( A D ( F ` n ) ) ^ 2 ) <_ ( ( S ^ 2 ) + ( 1 / n ) ) )

  disjoint n y
  disjoint F n
  disjoint F y
  disjoint J n
  disjoint J y
  disjoint M y
  disjoint N y
  disjoint n ph
  disjoint ph y
  disjoint S n
  disjoint S y
  disjoint A n
  disjoint A y
  disjoint D n
  disjoint D y
  disjoint U y
  disjoint W y
  disjoint X n
  disjoint Y n
  disjoint Y y
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint F j
  disjoint n x
  disjoint x y
  disjoint F x
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint J k
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint J w
  disjoint J x
  disjoint K y
  disjoint L y
  disjoint f j
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint M f
  disjoint j w
  disjoint M j
  disjoint M w
  disjoint M x
  disjoint N f
  disjoint N j
  disjoint N w
  disjoint N x
  disjoint f k
  disjoint f n
  disjoint f ph
  disjoint j k
  disjoint j ph
  disjoint k ph
  disjoint ph w
  disjoint ph x
  disjoint R w
  disjoint R x
  disjoint S f
  disjoint S k
  disjoint S w
  disjoint S x
  disjoint A f
  disjoint A j
  disjoint A k
  disjoint A w
  disjoint A x
  disjoint D f
  disjoint D j
  disjoint D k
  disjoint D w
  disjoint D x
  disjoint U w
  disjoint U x
  disjoint W w
  disjoint W x
  disjoint T n
  disjoint X j
  disjoint X k
  disjoint X w
  disjoint X x
  disjoint Y f
  disjoint Y j
  disjoint Y k
  disjoint Y w
  disjoint Y x
  assert |- ( ph -> ( ( ~~>t ` J ) ` F ) e. X )

  proof
    wph
    cY
    cX
    cF
    cJ
    clm
    cfv
    #
    cfv
    #
    wph
    cU
    cnv
    wcel
    #
    cW
    cU
    css
    cfv
    #
    wcel
    #
    cY
    cX
    wss
    #
    wph
    cU
    ccphlo
    wcel
    @2
    minveco.u
    cU
    phnv
    syl
    #
    wph
    @4
    cW
    ccbn
    wcel
    #
    wph
    cW
    @3
    ccbn
    cin
    wcel
    @4
    @7
    wa
    minveco.w
    cW
    @3
    ccbn
    elin
    sylib
    simpld
    cU
    @3
    cW
    cX
    cY
    minveco.x
    minveco.y
    @3
    eqid
    sspba
    syl2anc
    #
    wph
    @1
    cF
    cD
    cY
    cY
    cxp
    cres
    #
    cmopn
    cfv
    #
    clm
    cfv
    #
    cfv
    #
    cY
    wph
    @0
    wfun
    #
    cF
    @12
    @0
    wbr
    #
    @1
    @12
    wceq
    wph
    cJ
    cha
    wcel
    #
    @13
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @15
    wph
    @2
    @16
    @6
    cD
    cU
    cX
    minveco.x
    minveco.d
    imsxmet
    syl
    #
    cD
    cJ
    cX
    minveco.j
    methaus
    syl
    cJ
    lmfun
    syl
    wph
    @14
    cF
    @12
    @11
    wbr
    #
    wph
    vy
    cA
    cD
    cR
    cS
    cU
    vn
    cF
    cJ
    cM
    cN
    cW
    cX
    cY
    minveco.x
    minveco.m
    minveco.n
    minveco.y
    minveco.u
    minveco.w
    minveco.a
    minveco.d
    minveco.j
    minveco.r
    minveco.s
    minveco.f
    minveco.1
    minvecolem4a
    #
    wph
    @14
    cF
    @12
    cJ
    cY
    crest
    co
    #
    clm
    cfv
    #
    wbr
    @18
    wph
    @12
    cF
    cJ
    @20
    c1
    cvv
    cY
    cn
    @20
    eqid
    nnuz
    cY
    cvv
    wcel
    wph
    cY
    cW
    cba
    cfv
    cvv
    minveco.y
    cW
    cba
    fvex
    eqeltri
    a1i
    wph
    @16
    cJ
    ctop
    wcel
    @17
    cD
    cJ
    cX
    minveco.j
    mopntop
    syl
    wph
    @10
    cY
    ctopon
    cfv
    wcel
    #
    @18
    @12
    cY
    wcel
    wph
    @9
    cY
    cxmt
    cfv
    wcel
    #
    @22
    wph
    @16
    @5
    @23
    @17
    @8
    cD
    cY
    cX
    xmetres2
    syl2anc
    @9
    @10
    cY
    @10
    eqid
    #
    mopntopon
    syl
    @19
    @12
    cF
    @10
    cY
    lmcl
    syl2anc
    #
    wph
    1zzd
    minveco.f
    lmss
    wph
    @21
    @11
    cF
    @12
    wph
    @20
    @10
    clm
    wph
    @16
    @5
    @20
    @10
    wceq
    @17
    @8
    cD
    @9
    cJ
    @10
    cX
    cY
    @9
    eqid
    minveco.j
    @24
    metrest
    syl2anc
    fveq2d
    breqd
    bitrd
    mpbird
    cF
    @12
    @0
    funbrfv
    sylc
    @25
    eqeltrd
    sseldd
end
