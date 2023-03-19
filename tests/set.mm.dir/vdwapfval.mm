include "cn.mm"
include "cc0.mm"
include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cmul.mm"
include "caddc.mm"
include "cmpt.mm"
include "crn.mm"
include "cmpt2.mm"
include "cn0.mm"
include "cvdwa.mm"
include "wceq.mm"
include "wcel.mm"
include "w3a.mm"
include "simp1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "mpt2eq3dva.mm"
include "df-vdwap.mm"
include "nnex.mm"
include "mpt2ex.mm"
include "fvmpt.mm"

theorem vdwapfval
  let vm: setvar m
  let cK: class K
  let va: setvar a
  let vd: setvar d
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vk: setvar k
  let cX: class X

  disjoint a d
  disjoint a m
  disjoint d m
  disjoint K a
  disjoint K d
  disjoint K m
  disjoint a n
  disjoint a x
  disjoint A a
  disjoint d n
  disjoint d x
  disjoint A d
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint D a
  disjoint D d
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint a k
  disjoint d k
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint K k
  disjoint K n
  disjoint K x
  disjoint X m
  disjoint X x
  assert |- ( K e. NN0 -> ( AP ` K ) = ( a e. NN , d e. NN |-> ran ( m e. ( 0 ... ( K - 1 ) ) |-> ( a + ( m x. d ) ) ) ) )

  proof
    vk
    cK
    va
    vd
    cn
    cn
    vm
    cc0
    vk
    cv
    #
    c1
    cmin
    co
    #
    cfz
    co
    #
    va
    cv
    #
    vm
    cv
    vd
    cv
    #
    cmul
    co
    caddc
    co
    #
    cmpt
    #
    crn
    #
    cmpt2
    va
    vd
    cn
    cn
    vm
    cc0
    cK
    c1
    cmin
    co
    #
    cfz
    co
    #
    @5
    cmpt
    #
    crn
    #
    cmpt2
    cn0
    cvdwa
    @0
    cK
    wceq
    #
    va
    vd
    cn
    cn
    @7
    @11
    @12
    @3
    cn
    wcel
    #
    @4
    cn
    wcel
    #
    w3a
    #
    @6
    @10
    @15
    vm
    @2
    @9
    @5
    @15
    @1
    @8
    cc0
    cfz
    @15
    @0
    cK
    c1
    cmin
    @12
    @13
    @14
    simp1
    oveq1d
    oveq2d
    mpteq1d
    rneqd
    mpt2eq3dva
    vk
    vm
    va
    vd
    df-vdwap
    va
    vd
    cn
    cn
    @11
    nnex
    nnex
    mpt2ex
    fvmpt
end
