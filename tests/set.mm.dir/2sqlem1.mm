include "wcel.mm"
include "cgz.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "crn.mm"
include "wceq.mm"
include "wrex.mm"
include "eleq2i.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "ovex.mm"
include "elrnmpti.mm"
include "bitri.mm"

theorem 2sqlem1
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vy: setvar y
  let vz: setvar z
  let vm: setvar m
  let cC: class C
  let vu: setvar u
  let vv: setvar v
  let wph: wff ph
  let cB: class B
  let cM: class M
  let cD: class D
  let cE: class E
  let cN: class N
  let cY: class Y
  let cF: class F
  let cP: class P
  assume 2sq.1: |- S = ran ( w e. Z[i] |-> ( ( abs ` w ) ^ 2 ) )

  disjoint w x
  disjoint A x
  disjoint S x
  disjoint a b
  disjoint a n
  disjoint a p
  disjoint a q
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b n
  disjoint b p
  disjoint b q
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint n p
  disjoint n q
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint a m
  disjoint A a
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint A y
  disjoint A z
  disjoint C x
  disjoint p u
  disjoint p v
  disjoint p ph
  disjoint q u
  disjoint q v
  disjoint ph q
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint B a
  disjoint b m
  disjoint B b
  disjoint m p
  disjoint B m
  disjoint B p
  disjoint B x
  disjoint B y
  disjoint a u
  disjoint a v
  disjoint M a
  disjoint b u
  disjoint b v
  disjoint M b
  disjoint M p
  disjoint u z
  disjoint M u
  disjoint v z
  disjoint M v
  disjoint M x
  disjoint M y
  disjoint M z
  disjoint S a
  disjoint S b
  disjoint m n
  disjoint m q
  disjoint m u
  disjoint m v
  disjoint S m
  disjoint n u
  disjoint n v
  disjoint S n
  disjoint S p
  disjoint S q
  disjoint S u
  disjoint S v
  disjoint S y
  disjoint S z
  disjoint D x
  disjoint E a
  disjoint E p
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint N p
  disjoint N q
  disjoint N u
  disjoint N v
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint Y a
  disjoint Y b
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint F a
  disjoint F p
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint P n
  disjoint P p
  disjoint P q
  disjoint P x
  disjoint P y
  assert |- ( A e. S <-> E. x e. Z[i] A = ( ( abs ` x ) ^ 2 ) )

  proof
    cA
    cS
    wcel
    cA
    vw
    cgz
    vw
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    cmpt
    #
    crn
    #
    wcel
    cA
    vx
    cv
    #
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    wceq
    vx
    cgz
    wrex
    cS
    @4
    cA
    2sq.1
    eleq2i
    vx
    cgz
    @7
    cA
    @3
    vw
    vx
    cgz
    @2
    @7
    @0
    @5
    wceq
    @1
    @6
    c2
    cexp
    @0
    @5
    cabs
    fveq2
    oveq1d
    cbvmptv
    @6
    c2
    cexp
    ovex
    elrnmpti
    bitri
end
