include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cc.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "coeid.mm"
include "fveq1d.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "sumeq2sdv.mm"
include "eqid.mm"
include "sumex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem coeid2
  let cA: class A
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cN: class N
  let cX: class X
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let wph: wff ph
  let vm: setvar m
  let cB: class B
  let cM: class M
  assume dgrub.1: |- A = ( coeff ` F )
  assume dgrub.2: |- N = ( deg ` F )

  disjoint A k
  disjoint F k
  disjoint S k
  disjoint N k
  disjoint X k
  disjoint a k
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F a
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint k ph
  disjoint ph z
  disjoint a m
  disjoint S a
  disjoint k m
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint S m
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint B k
  disjoint B z
  disjoint M k
  disjoint M y
  disjoint M z
  disjoint N a
  disjoint N n
  disjoint N z
  disjoint X z
  disjoint F z
  assert |- ( ( F e. ( Poly ` S ) /\ X e. CC ) -> ( F ` X ) = sum_ k e. ( 0 ... N ) ( ( A ` k ) x. ( X ^ k ) ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cX
    cc
    wcel
    cX
    cF
    cfv
    cX
    vz
    cc
    cc0
    cN
    cfz
    co
    #
    vk
    cv
    #
    cA
    cfv
    #
    vz
    cv
    #
    @2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    cmpt
    #
    cfv
    @1
    @3
    cX
    @2
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    @0
    cX
    cF
    @8
    vz
    cA
    cS
    vk
    cF
    cN
    dgrub.1
    dgrub.2
    coeid
    fveq1d
    vz
    cX
    @7
    @11
    cc
    @8
    @4
    cX
    wceq
    #
    @1
    @6
    @10
    vk
    @12
    @5
    @9
    @3
    cmul
    @4
    cX
    @2
    cexp
    oveq1
    oveq2d
    sumeq2sdv
    @8
    eqid
    @1
    @10
    vk
    sumex
    fvmpt
    sylan9eq
end
