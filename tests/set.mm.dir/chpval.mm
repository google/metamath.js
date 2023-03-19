include "c1.mm"
include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cvma.mm"
include "csu.mm"
include "cr.mm"
include "cchp.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "sumeq1d.mm"
include "df-chp.mm"
include "sumex.mm"
include "fvmpt.mm"

theorem chpval
  let cA: class A
  let vn: setvar n
  let vk: setvar k
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P

  disjoint A n
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q s
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint K p
  disjoint M p
  disjoint M x
  disjoint N p
  disjoint S s
  disjoint S x
  disjoint B k
  disjoint B n
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint P p
  assert |- ( A e. RR -> ( psi ` A ) = sum_ n e. ( 1 ... ( |_ ` A ) ) ( Lam ` n ) )

  proof
    vx
    cA
    c1
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    vn
    cv
    cvma
    cfv
    #
    vn
    csu
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    @3
    vn
    csu
    cr
    cchp
    @0
    cA
    wceq
    #
    @2
    @5
    @3
    vn
    @6
    @1
    @4
    c1
    cfz
    @0
    cA
    cfl
    fveq2
    oveq2d
    sumeq1d
    vx
    vn
    df-chp
    @5
    @3
    vn
    sumex
    fvmpt
end
