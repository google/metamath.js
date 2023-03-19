include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "w3a.mm"
include "cvdwa.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wrex.mm"
include "cab.mm"
include "cmpt.mm"
include "crn.mm"
include "cmpt2.mm"
include "vdwapfval.mm"
include "3ad2ant1.mm"
include "oveqd.mm"
include "wa.mm"
include "oveq2.mm"
include "oveq12.mm"
include "sylan2.mm"
include "mpteq2dv.mm"
include "rneqd.mm"
include "eqid.mm"
include "ovex.mm"
include "mptex.mm"
include "rnex.mm"
include "ovmpt2a.mm"
include "3adant1.mm"
include "eqtrd.mm"
include "rnmpt.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "cvv.mm"
include "id.mm"
include "syl6eqel.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab3.mm"
include "syl6bb.mm"

theorem vdwapval
  let cA: class A
  let cD: class D
  let vm: setvar m
  let cK: class K
  let cX: class X
  let va: setvar a
  let vd: setvar d
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k

  disjoint A m
  disjoint D m
  disjoint K m
  disjoint X m
  disjoint a d
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint A a
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint A d
  disjoint m n
  disjoint m x
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint D a
  disjoint D d
  disjoint D n
  disjoint D x
  disjoint a k
  disjoint K a
  disjoint d k
  disjoint K d
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint K k
  disjoint K n
  disjoint K x
  disjoint X x
  assert |- ( ( K e. NN0 /\ A e. NN /\ D e. NN ) -> ( X e. ( A ( AP ` K ) D ) <-> E. m e. ( 0 ... ( K - 1 ) ) X = ( A + ( m x. D ) ) ) )

  proof
    cK
    cn0
    wcel
    #
    cA
    cn
    wcel
    #
    cD
    cn
    wcel
    #
    w3a
    #
    cX
    cA
    cD
    cK
    cvdwa
    cfv
    #
    co
    #
    wcel
    cX
    vx
    cv
    #
    cA
    vm
    cv
    #
    cD
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
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
    wrex
    #
    vx
    cab
    #
    wcel
    cX
    @9
    wceq
    #
    vm
    @12
    wrex
    #
    @3
    @5
    @14
    cX
    @3
    @5
    vm
    @12
    @9
    cmpt
    #
    crn
    #
    @14
    @3
    @5
    cA
    cD
    va
    vd
    cn
    cn
    vm
    @12
    va
    cv
    #
    @7
    vd
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    crn
    #
    cmpt2
    #
    co
    #
    @18
    @3
    @4
    @25
    cA
    cD
    @0
    @1
    @4
    @25
    wceq
    @2
    vm
    cK
    va
    vd
    vdwapfval
    3ad2ant1
    oveqd
    @1
    @2
    @26
    @18
    wceq
    @0
    va
    vd
    cA
    cD
    cn
    cn
    @24
    @18
    @25
    @19
    cA
    wceq
    #
    @20
    cD
    wceq
    #
    wa
    #
    @23
    @17
    @29
    vm
    @12
    @22
    @9
    @28
    @27
    @21
    @8
    wceq
    @22
    @9
    wceq
    @20
    cD
    @7
    cmul
    oveq2
    @19
    cA
    @21
    @8
    caddc
    oveq12
    sylan2
    mpteq2dv
    rneqd
    @25
    eqid
    @17
    vm
    @12
    @9
    cc0
    @11
    cfz
    ovex
    mptex
    rnex
    ovmpt2a
    3adant1
    eqtrd
    vm
    vx
    @12
    @9
    @17
    @17
    eqid
    rnmpt
    syl6eq
    eleq2d
    @13
    @16
    vx
    cX
    @15
    cX
    cvv
    wcel
    vm
    @12
    @15
    cX
    @9
    cvv
    @15
    id
    cA
    @8
    caddc
    ovex
    syl6eqel
    rexlimivw
    @6
    cX
    wceq
    @10
    @15
    vm
    @12
    @6
    cX
    @9
    eqeq1
    rexbidv
    elab3
    syl6bb
end
