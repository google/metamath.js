include "cho.mm"
include "wcel.mm"
include "wa.mm"
include "cleo.mm"
include "wbr.mm"
include "chod.mm"
include "co.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "cle.mm"
include "chil.mm"
include "wral.mm"
include "leopg.mm"
include "hmopd.mm"
include "ancoms.mm"
include "biantrurd.mm"
include "bitr4d.mm"

theorem leop
  let vx: setvar x
  let cT: class T
  let cU: class U
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let vt: setvar t
  let vu: setvar u

  disjoint T x
  disjoint U x
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint A x
  disjoint y z
  disjoint w y
  disjoint A y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B x
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
  assert |- ( ( T e. HrmOp /\ U e. HrmOp ) -> ( T <_op U <-> A. x e. ~H 0 <_ ( ( ( U -op T ) ` x ) .ih x ) ) )

  proof
    cT
    cho
    wcel
    #
    cU
    cho
    wcel
    #
    wa
    #
    cT
    cU
    cleo
    wbr
    cU
    cT
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
    @3
    cfv
    @5
    csp
    co
    cle
    wbr
    vx
    chil
    wral
    #
    wa
    @6
    vx
    cho
    cho
    cT
    cU
    leopg
    @2
    @4
    @6
    @1
    @0
    @4
    cU
    cT
    hmopd
    ancoms
    biantrurd
    bitr4d
end
