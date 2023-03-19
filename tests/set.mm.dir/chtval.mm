include "cc0.mm"
include "cv.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "clog.mm"
include "cfv.mm"
include "csu.mm"
include "cr.mm"
include "ccht.mm"
include "wceq.mm"
include "oveq2.mm"
include "ineq1d.mm"
include "sumeq1d.mm"
include "df-cht.mm"
include "sumex.mm"
include "fvmpt.mm"

theorem chtval
  let cA: class A
  let vp: setvar p
  let vk: setvar k
  let vn: setvar n
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

  disjoint A p
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
  disjoint A n
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p y
  disjoint p z
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
  assert |- ( A e. RR -> ( theta ` A ) = sum_ p e. ( ( 0 [,] A ) i^i Prime ) ( log ` p ) )

  proof
    vx
    cA
    cc0
    vx
    cv
    #
    cicc
    co
    #
    cprime
    cin
    #
    vp
    cv
    clog
    cfv
    #
    vp
    csu
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    @3
    vp
    csu
    cr
    ccht
    @0
    cA
    wceq
    #
    @2
    @5
    @3
    vp
    @6
    @1
    @4
    cprime
    @0
    cA
    cc0
    cicc
    oveq2
    ineq1d
    sumeq1d
    vx
    vp
    df-cht
    @5
    @3
    vp
    sumex
    fvmpt
end
