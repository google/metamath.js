include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "oveq1.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "infeq1d.mm"
include "xrltso.mm"
include "infex.mm"
include "fvmpt.mm"

theorem metdsval
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cS: class S
  let cF: class F
  let cX: class X
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let vs: setvar s
  let vt: setvar t
  let cJ: class J
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cG: class G
  let cR: class R
  let cT: class T
  let cK: class K
  let cU: class U
  let cV: class V
  assume metdscn.f: |- F = ( x e. X |-> inf ( ran ( y e. S |-> ( x D y ) ) , RR* , < ) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint r s
  disjoint r t
  disjoint D r
  disjoint s t
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint D s
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint D t
  disjoint D w
  disjoint D z
  disjoint J r
  disjoint J s
  disjoint J t
  disjoint J w
  disjoint J y
  disjoint J z
  disjoint ph s
  disjoint ph t
  disjoint B x
  disjoint B y
  disjoint C r
  disjoint C s
  disjoint C w
  disjoint C z
  disjoint G s
  disjoint G t
  disjoint R w
  disjoint R z
  disjoint T s
  disjoint T t
  disjoint T w
  disjoint T x
  disjoint T y
  disjoint T z
  disjoint K r
  disjoint K s
  disjoint K w
  disjoint K z
  disjoint S r
  disjoint S s
  disjoint S t
  disjoint S w
  disjoint S z
  disjoint U s
  disjoint U w
  disjoint X r
  disjoint X s
  disjoint X t
  disjoint X w
  disjoint X z
  disjoint F r
  disjoint F s
  disjoint F t
  disjoint F w
  disjoint F z
  disjoint V w
  disjoint V z
  assert |- ( A e. X -> ( F ` A ) = inf ( ran ( y e. S |-> ( A D y ) ) , RR* , < ) )

  proof
    vx
    cA
    vy
    cS
    vx
    cv
    #
    vy
    cv
    #
    cD
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    vy
    cS
    cA
    @1
    cD
    co
    #
    cmpt
    #
    crn
    #
    cxr
    clt
    cinf
    cX
    cF
    @0
    cA
    wceq
    #
    cxr
    @4
    @7
    clt
    @8
    @3
    @6
    @8
    vy
    cS
    @2
    @5
    @0
    cA
    @1
    cD
    oveq1
    mpteq2dv
    rneqd
    infeq1d
    metdscn.f
    cxr
    @7
    clt
    xrltso
    infex
    fvmpt
end
