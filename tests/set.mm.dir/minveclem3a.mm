include "cress.mm"
include "co.mm"
include "cds.mm"
include "cfv.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cms.mm"
include "ccms.mm"
include "wcel.mm"
include "eqid.mm"
include "cmscmet.mm"
include "syl.mm"
include "reseq1i.mm"
include "wss.mm"
include "clss.mm"
include "lssss.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "resabs1d.mm"
include "wceq.mm"
include "ressds.mm"
include "ressbas2.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "3eltr4d.mm"

theorem minveclem3a
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let cJ: class J
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

  disjoint .- y
  disjoint A y
  disjoint J y
  disjoint N y
  disjoint ph y
  disjoint R y
  disjoint U y
  disjoint X y
  disjoint Y y
  disjoint D y
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
  disjoint K y
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
  disjoint L y
  assert |- ( ph -> ( D |` ( Y X. Y ) ) e. ( CMet ` Y ) )

  proof
    wph
    cU
    cY
    cress
    co
    #
    cds
    cfv
    #
    @0
    cbs
    cfv
    #
    @2
    cxp
    #
    cres
    #
    @2
    cms
    cfv
    #
    cD
    cY
    cY
    cxp
    #
    cres
    #
    cY
    cms
    cfv
    wph
    @0
    ccms
    wcel
    @4
    @5
    wcel
    minvec.w
    @4
    @0
    @2
    @2
    eqid
    @4
    eqid
    cmscmet
    syl
    wph
    @7
    cU
    cds
    cfv
    #
    cX
    cX
    cxp
    #
    cres
    #
    @6
    cres
    #
    @4
    cD
    @10
    @6
    minvec.d
    reseq1i
    wph
    @11
    @8
    @6
    cres
    @4
    wph
    @8
    @6
    @9
    wph
    cY
    cX
    wss
    #
    @12
    @6
    @9
    wss
    wph
    cY
    cU
    clss
    cfv
    #
    wcel
    #
    @12
    minvec.y
    @13
    cY
    cX
    cU
    minvec.x
    @13
    eqid
    lssss
    syl
    #
    @15
    cY
    cX
    cY
    cX
    xpss12
    syl2anc
    resabs1d
    wph
    @8
    @1
    @6
    @3
    wph
    @14
    @8
    @1
    wceq
    minvec.y
    cY
    @8
    cU
    @0
    @13
    @0
    eqid
    #
    @8
    eqid
    ressds
    syl
    wph
    cY
    @2
    wph
    @12
    cY
    @2
    wceq
    @15
    cY
    cX
    @0
    cU
    @16
    minvec.x
    ressbas2
    syl
    #
    sqxpeqd
    reseq12d
    eqtrd
    syl5eq
    wph
    cY
    @2
    cms
    @17
    fveq2d
    3eltr4d
end
