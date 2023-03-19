include "cv.mm"
include "chil.mm"
include "wcel.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "crio.mm"
include "wreu.mm"
include "clf.mm"
include "ccnfn.mm"
include "cin.mm"
include "wa.mm"
include "cnlnadjlem2.mm"
include "elin.mm"
include "sylibr.mm"
include "riesz4.mm"
include "syl.mm"
include "cnlnadjlem1.mm"
include "eqeq1d.mm"
include "ralbiia.mm"
include "reubii.mm"
include "sylib.mm"
include "riotacl.mm"
include "syl5eqel.mm"

theorem cnlnadjlem3
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let cB: class B
  let cT: class T
  let vg: setvar g
  let cG: class G
  let vf: setvar f
  let vz: setvar z
  let cA: class A
  let vt: setvar t
  let vx: setvar x
  let cF: class F
  let cC: class C
  assume cnlnadjlem.1: |- T e. LinOp
  assume cnlnadjlem.2: |- T e. ContOp
  assume cnlnadjlem.3: |- G = ( g e. ~H |-> ( ( T ` g ) .ih y ) )
  assume cnlnadjlem.4: |- B = ( iota_ w e. ~H A. v e. ~H ( ( T ` v ) .ih y ) = ( v .ih w ) )

  disjoint g v
  disjoint g w
  disjoint g y
  disjoint v w
  disjoint v y
  disjoint w y
  disjoint T g
  disjoint T v
  disjoint T w
  disjoint T y
  disjoint G v
  disjoint G w
  disjoint f g
  disjoint f v
  disjoint f w
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g z
  disjoint A g
  disjoint v z
  disjoint A v
  disjoint w z
  disjoint A w
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B z
  disjoint f t
  disjoint f x
  disjoint F f
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint F t
  disjoint w x
  disjoint F w
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint T f
  disjoint g t
  disjoint g x
  disjoint t v
  disjoint t y
  disjoint T t
  disjoint v x
  disjoint x y
  disjoint T x
  disjoint T z
  disjoint C f
  disjoint G f
  disjoint G x
  disjoint G z
  assert |- ( y e. ~H -> B e. ~H )

  proof
    vy
    cv
    #
    chil
    wcel
    #
    cB
    vv
    cv
    #
    cT
    cfv
    @0
    csp
    co
    #
    @2
    vw
    cv
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    vw
    chil
    crio
    #
    chil
    cnlnadjlem.4
    @1
    @6
    vw
    chil
    wreu
    #
    @7
    chil
    wcel
    @1
    @2
    cG
    cfv
    #
    @4
    wceq
    #
    vv
    chil
    wral
    #
    vw
    chil
    wreu
    #
    @8
    @1
    cG
    clf
    ccnfn
    cin
    wcel
    #
    @12
    @1
    cG
    clf
    wcel
    cG
    ccnfn
    wcel
    wa
    @13
    vy
    cT
    vg
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem2
    cG
    clf
    ccnfn
    elin
    sylibr
    vw
    vv
    cG
    riesz4
    syl
    @11
    @6
    vw
    chil
    @10
    @5
    vv
    chil
    @2
    chil
    wcel
    @9
    @3
    @4
    vy
    @2
    cT
    vg
    cG
    cnlnadjlem.1
    cnlnadjlem.2
    cnlnadjlem.3
    cnlnadjlem1
    eqeq1d
    ralbiia
    reubii
    sylib
    @6
    vw
    chil
    riotacl
    syl
    syl5eqel
end
