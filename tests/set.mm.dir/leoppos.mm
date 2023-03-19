include "cho.mm"
include "wcel.mm"
include "ch0o.mm"
include "cleo.mm"
include "wbr.mm"
include "cc0.mm"
include "cv.mm"
include "chod.mm"
include "co.mm"
include "cfv.mm"
include "csp.mm"
include "cle.mm"
include "chil.mm"
include "wral.mm"
include "wb.mm"
include "0hmop.mm"
include "leop.mm"
include "mpan.mm"
include "wf.mm"
include "wceq.mm"
include "hmopf.mm"
include "hosubid1.mm"
include "syl.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "bitrd.mm"

theorem leoppos
  let vx: setvar x
  let cT: class T
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
  let cU: class U

  disjoint T x
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
  disjoint U x
  disjoint t z
  assert |- ( T e. HrmOp -> ( 0hop <_op T <-> A. x e. ~H 0 <_ ( ( T ` x ) .ih x ) ) )

  proof
    cT
    cho
    wcel
    #
    ch0o
    cT
    cleo
    wbr
    #
    cc0
    vx
    cv
    #
    cT
    ch0o
    chod
    co
    #
    cfv
    #
    @2
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
    cc0
    @2
    cT
    cfv
    #
    @2
    csp
    co
    #
    cle
    wbr
    #
    vx
    chil
    wral
    ch0o
    cho
    wcel
    @0
    @1
    @7
    wb
    0hmop
    vx
    ch0o
    cT
    leop
    mpan
    @0
    @6
    @10
    vx
    chil
    @0
    @5
    @9
    cc0
    cle
    @0
    @4
    @8
    @2
    csp
    @0
    @2
    @3
    cT
    @0
    chil
    chil
    cT
    wf
    @3
    cT
    wceq
    cT
    hmopf
    cT
    hosubid1
    syl
    fveq1d
    oveq1d
    breq2d
    ralbidv
    bitrd
end
