include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cmul.mm"
include "cof.mm"
include "co.mm"
include "ccoe.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cmin.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "cmpt.mm"
include "cdgr.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "eqid.mm"
include "coemullem.mm"
include "simpld.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "adantr.mm"
include "sumeq12dv.mm"
include "sumex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "3impa.mm"

theorem coemul
  let cA: class A
  let cB: class B
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cN: class N
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cM: class M
  assume coefv0.1: |- A = ( coeff ` F )
  assume coeadd.2: |- B = ( coeff ` G )

  disjoint A k
  disjoint B k
  disjoint F k
  disjoint G k
  disjoint N k
  disjoint S k
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
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
  disjoint B j
  disjoint B n
  disjoint B y
  disjoint B z
  disjoint F j
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint M j
  disjoint M k
  disjoint M z
  disjoint G j
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint N j
  disjoint N n
  disjoint N z
  disjoint S j
  disjoint S n
  disjoint S x
  disjoint S y
  disjoint S z
  assert |- ( ( F e. ( Poly ` S ) /\ G e. ( Poly ` S ) /\ N e. NN0 ) -> ( ( coeff ` ( F oF x. G ) ) ` N ) = sum_ k e. ( 0 ... N ) ( ( A ` k ) x. ( B ` ( N - k ) ) ) )

  proof
    cF
    cS
    cply
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    cN
    cn0
    wcel
    #
    cN
    cF
    cG
    cmul
    cof
    co
    #
    ccoe
    cfv
    #
    cfv
    #
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
    cN
    @8
    cmin
    co
    #
    cB
    cfv
    #
    cmul
    co
    #
    vk
    csu
    #
    wceq
    @1
    @2
    wa
    #
    @3
    @6
    cN
    vn
    cn0
    cc0
    vn
    cv
    #
    cfz
    co
    #
    @9
    @15
    @8
    cmin
    co
    #
    cB
    cfv
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
    @13
    @14
    cN
    @5
    @21
    @14
    @5
    @21
    wceq
    @4
    cdgr
    cfv
    cF
    cdgr
    cfv
    #
    cG
    cdgr
    cfv
    #
    caddc
    co
    cle
    wbr
    cA
    cB
    cS
    vk
    vn
    cF
    cG
    @22
    @23
    coefv0.1
    coeadd.2
    @22
    eqid
    @23
    eqid
    coemullem
    simpld
    fveq1d
    vn
    cN
    @20
    @13
    cn0
    @21
    @15
    cN
    wceq
    #
    @16
    @7
    @19
    @12
    vk
    @15
    cN
    cc0
    cfz
    oveq2
    @24
    @19
    @12
    wceq
    @8
    @16
    wcel
    @24
    @18
    @11
    @9
    cmul
    @24
    @17
    @10
    cB
    @15
    cN
    @8
    cmin
    oveq1
    fveq2d
    oveq2d
    adantr
    sumeq12dv
    @21
    eqid
    @7
    @12
    vk
    sumex
    fvmpt
    sylan9eq
    3impa
end
