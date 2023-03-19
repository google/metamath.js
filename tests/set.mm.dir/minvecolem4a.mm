include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "cfv.mm"
include "clm.mm"
include "cdm.mm"
include "wcel.mm"
include "wbr.mm"
include "cba.mm"
include "cms.mm"
include "cca.mm"
include "cims.mm"
include "cnv.mm"
include "css.mm"
include "wceq.mm"
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
include "sspims.mm"
include "syl2anc.mm"
include "simprd.mm"
include "cbncms.mm"
include "eqeltrrd.mm"
include "minvecolem3.mm"
include "cxmt.mm"
include "cn.mm"
include "wf.mm"
include "wb.mm"
include "cme.mm"
include "imsmet.mm"
include "3syl.mm"
include "metxmet.mm"
include "causs.mm"
include "mpbid.mm"
include "cmetcau.mm"
include "cha.mm"
include "wfun.mm"
include "xmetres.mm"
include "methaus.mm"
include "lmfun.mm"
include "funfvbrb.mm"

theorem minvecolem4a
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
  assert |- ( ph -> F ( ~~>t ` ( MetOpen ` ( D |` ( Y X. Y ) ) ) ) ( ( ~~>t ` ( MetOpen ` ( D |` ( Y X. Y ) ) ) ) ` F ) )

  proof
    wph
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
    cdm
    wcel
    #
    cF
    cF
    @2
    cfv
    @2
    wbr
    #
    wph
    @0
    cW
    cba
    cfv
    #
    cms
    cfv
    #
    wcel
    cF
    @0
    cca
    cfv
    wcel
    #
    @3
    wph
    cW
    cims
    cfv
    #
    @0
    @6
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
    @8
    @0
    wceq
    wph
    cU
    ccphlo
    wcel
    #
    @9
    minveco.u
    cU
    phnv
    #
    syl
    wph
    @11
    cW
    ccbn
    wcel
    #
    wph
    cW
    @10
    ccbn
    cin
    wcel
    @11
    @14
    wa
    minveco.w
    cW
    @10
    ccbn
    elin
    sylib
    #
    simpld
    @8
    cD
    cU
    @10
    cW
    cY
    minveco.y
    minveco.d
    @8
    eqid
    #
    @10
    eqid
    sspims
    syl2anc
    wph
    @14
    @8
    @6
    wcel
    wph
    @11
    @14
    @15
    simprd
    @8
    cW
    @5
    @5
    eqid
    @16
    cbncms
    syl
    eqeltrrd
    wph
    cF
    cD
    cca
    cfv
    wcel
    #
    @7
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
    minvecolem3
    wph
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cn
    cY
    cF
    wf
    @17
    @7
    wb
    wph
    cD
    cX
    cme
    cfv
    wcel
    #
    @18
    wph
    @12
    @9
    @19
    minveco.u
    @13
    cD
    cU
    cX
    minveco.x
    minveco.d
    imsmet
    3syl
    cD
    cX
    metxmet
    syl
    #
    minveco.f
    cD
    cF
    cX
    cY
    causs
    syl2anc
    mpbid
    @0
    cF
    @1
    @5
    @1
    eqid
    #
    cmetcau
    syl2anc
    wph
    @1
    cha
    wcel
    #
    @2
    wfun
    @3
    @4
    wb
    wph
    @18
    @0
    cX
    cY
    cin
    #
    cxmt
    cfv
    wcel
    @22
    @20
    cD
    cY
    cX
    xmetres
    @0
    @1
    @23
    @21
    methaus
    3syl
    @1
    lmfun
    cF
    @2
    funfvbrb
    3syl
    mpbid
end
