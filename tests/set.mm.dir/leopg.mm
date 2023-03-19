include "cv.mm"
include "chod.mm"
include "co.mm"
include "cho.mm"
include "wcel.mm"
include "cc0.mm"
include "cfv.mm"
include "csp.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "wa.mm"
include "cleo.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "oveq1.mm"
include "df-leop.mm"
include "brabg.mm"

theorem leopg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  let cU: class U
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u

  disjoint A x
  disjoint B x
  disjoint T x
  disjoint U x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint S x
  disjoint t u
  disjoint t x
  disjoint t y
  disjoint T t
  disjoint u x
  disjoint u y
  disjoint T u
  disjoint T y
  disjoint U t
  disjoint U u
  disjoint t z
  assert |- ( ( T e. A /\ U e. B ) -> ( T <_op U <-> ( ( U -op T ) e. HrmOp /\ A. x e. ~H 0 <_ ( ( ( U -op T ) ` x ) .ih x ) ) ) )

  proof
    vu
    cv
    #
    vt
    cv
    #
    chod
    co
    #
    cho
    wcel
    #
    cc0
    vx
    cv
    #
    @2
    cfv
    #
    @4
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    wa
    @0
    cT
    chod
    co
    #
    cho
    wcel
    #
    cc0
    @4
    @9
    cfv
    #
    @4
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    wa
    cU
    cT
    chod
    co
    #
    cho
    wcel
    #
    cc0
    @4
    @15
    cfv
    #
    @4
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    #
    wa
    vt
    vu
    cT
    cU
    cA
    cB
    cleo
    @1
    cT
    wceq
    #
    @3
    @10
    @8
    @14
    @21
    @2
    @9
    cho
    @1
    cT
    @0
    chod
    oveq2
    #
    eleq1d
    @21
    @7
    @13
    vx
    chil
    @21
    @6
    @12
    cc0
    cle
    @21
    @5
    @11
    @4
    csp
    @21
    @4
    @2
    @9
    @22
    fveq1d
    oveq1d
    breq2d
    ralbidv
    anbi12d
    @0
    cU
    wceq
    #
    @10
    @16
    @14
    @20
    @23
    @9
    @15
    cho
    @0
    cU
    cT
    chod
    oveq1
    #
    eleq1d
    @23
    @13
    @19
    vx
    chil
    @23
    @12
    @18
    cc0
    cle
    @23
    @11
    @17
    @4
    csp
    @23
    @4
    @9
    @15
    @24
    fveq1d
    oveq1d
    breq2d
    ralbidv
    anbi12d
    vx
    vu
    vt
    df-leop
    brabg
end
