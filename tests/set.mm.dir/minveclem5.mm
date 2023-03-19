include "crp.mm"
include "cv.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "cflim.mm"
include "cuni.mm"
include "cdiv.mm"
include "cmin.mm"
include "weq.mm"
include "oveq2.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "syl6eq.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "eqid.mm"
include "minveclem4.mm"

theorem minveclem5
  let wph: wff ph
  let vx: setvar x
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

  disjoint x y
  disjoint .- x
  disjoint .- y
  disjoint A x
  disjoint A y
  disjoint J x
  disjoint J y
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint R x
  disjoint R y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint S y
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
  disjoint D z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S z
  disjoint T r
  disjoint T y
  disjoint L y
  assert |- ( ph -> E. x e. Y A. y e. Y ( N ` ( A .- x ) ) <_ ( N ` ( A .- y ) ) )

  proof
    wph
    vx
    vy
    cA
    cD
    cJ
    cX
    vs
    crp
    cA
    vz
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
    vs
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vz
    cY
    crab
    #
    cmpt
    #
    crn
    #
    cfg
    co
    cflim
    co
    cuni
    #
    cR
    cS
    cA
    @10
    cD
    co
    cS
    caddc
    co
    c2
    cdiv
    co
    c2
    cexp
    co
    @3
    cmin
    co
    #
    cU
    @9
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
    @8
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
    @3
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
    vs
    vr
    crp
    @7
    @18
    vs
    vr
    weq
    #
    @7
    @2
    @16
    cle
    wbr
    #
    vz
    cY
    crab
    @18
    @19
    @6
    @20
    vz
    cY
    @19
    @5
    @16
    @2
    cle
    @4
    @15
    @3
    caddc
    oveq2
    breq2d
    rabbidv
    @20
    @17
    vz
    vy
    cY
    vz
    vy
    weq
    #
    @2
    @14
    @16
    cle
    @21
    @1
    @13
    c2
    cexp
    @0
    @12
    cA
    cD
    oveq2
    oveq1d
    breq1d
    cbvrabv
    syl6eq
    cbvmptv
    rneqi
    @10
    eqid
    @11
    eqid
    minveclem4
end
