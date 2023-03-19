include "cds.mm"
include "cfv.mm"
include "cxp.mm"
include "cres.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "ctopn.mm"
include "eqid.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "minveclem7.mm"

theorem minvec
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cU: class U
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vw: setvar w
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cJ: class J
  let cP: class P
  let cF: class F
  let cK: class K
  let cR: class R
  let cD: class D
  let cS: class S
  let cT: class T
  let cL: class L
  assume minvec.x: |- X = ( Base ` U )
  assume minvec.m: |- .- = ( -g ` U )
  assume minvec.n: |- N = ( norm ` U )
  assume minvec.u: |- ( ph -> U e. CPreHil )
  assume minvec.y: |- ( ph -> Y e. ( LSubSp ` U ) )
  assume minvec.w: |- ( ph -> ( U |`s Y ) e. CMetSp )
  assume minvec.a: |- ( ph -> A e. X )

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint A x
  disjoint A y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
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
  disjoint y z
  disjoint A z
  disjoint J r
  disjoint J w
  disjoint J x
  disjoint J y
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
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint U w
  disjoint X r
  disjoint X w
  disjoint Y j
  disjoint Y r
  disjoint Y s
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y z
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint T r
  disjoint T y
  disjoint L y
  assert |- ( ph -> E! x e. Y A. y e. Y ( N ` ( A .- x ) ) <_ ( N ` ( A .- y ) ) )

  proof
    wph
    vx
    vy
    cA
    cU
    cds
    cfv
    cX
    cX
    cxp
    cres
    #
    vj
    cY
    cA
    vj
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
    @5
    cr
    clt
    cinf
    #
    cU
    cU
    ctopn
    cfv
    #
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
    @7
    eqid
    @4
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
    vj
    vy
    cY
    @3
    @10
    @1
    @8
    wceq
    @2
    @9
    cN
    @1
    @8
    cA
    c.mi
    oveq2
    fveq2d
    cbvmptv
    rneqi
    @6
    eqid
    @0
    eqid
    minveclem7
end
