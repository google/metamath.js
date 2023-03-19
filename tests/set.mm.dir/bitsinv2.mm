include "cn0.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "csu.mm"
include "cbits.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wss.mm"
include "elfpw.mm"
include "simprbi.mm"
include "wa.mm"
include "2nn0.mm"
include "a1i.mm"
include "simplbi.mm"
include "sselda.mm"
include "nn0expcld.mm"
include "fsumnn0cl.mm"
include "bitsinv1.mm"
include "syl.mm"
include "bitsss.mm"
include "bitsfi.mm"
include "sylanbrc.mm"
include "oveq2.mm"
include "cbvsumv.mm"
include "sumeq1.mm"
include "syl5eq.mm"
include "eqid.mm"
include "sumex.mm"
include "fvmpt.mm"
include "3eqtr4d.mm"
include "wf1.mm"
include "wb.mm"
include "wf1o.mm"
include "ackbijnn.mm"
include "f1of1.mm"
include "mp1i.mm"
include "id.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "mpbid.mm"

theorem bitsinv2
  let cA: class A
  let vn: setvar n
  let vk: setvar k
  let vm: setvar m
  let vx: setvar x
  let vy: setvar y
  let cN: class N

  disjoint A n
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n x
  disjoint A x
  disjoint k y
  disjoint N k
  disjoint n y
  disjoint N n
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( A e. ( ~P NN0 i^i Fin ) -> ( bits ` sum_ n e. A ( 2 ^ n ) ) = A )

  proof
    cA
    cn0
    cpw
    cfn
    cin
    #
    wcel
    #
    cA
    c2
    vn
    cv
    #
    cexp
    co
    #
    vn
    csu
    #
    cbits
    cfv
    #
    vk
    @0
    vk
    cv
    #
    @3
    vn
    csu
    #
    cmpt
    #
    cfv
    #
    cA
    @8
    cfv
    #
    wceq
    #
    @5
    cA
    wceq
    #
    @1
    @5
    c2
    vm
    cv
    #
    cexp
    co
    #
    vm
    csu
    #
    @4
    @9
    @10
    @1
    @4
    cn0
    wcel
    #
    @15
    @4
    wceq
    @1
    cA
    @3
    vn
    @1
    cA
    cn0
    wss
    #
    cA
    cfn
    wcel
    #
    cA
    cn0
    elfpw
    #
    simprbi
    @1
    @2
    cA
    wcel
    wa
    #
    c2
    @2
    c2
    cn0
    wcel
    @20
    2nn0
    a1i
    @1
    cA
    cn0
    @2
    @1
    @17
    @18
    @19
    simplbi
    sselda
    nn0expcld
    fsumnn0cl
    #
    vm
    @4
    bitsinv1
    syl
    @1
    @5
    @0
    wcel
    #
    @9
    @15
    wceq
    @1
    @5
    cn0
    wss
    #
    @5
    cfn
    wcel
    #
    @22
    @23
    @1
    @4
    bitsss
    a1i
    @1
    @16
    @24
    @21
    @4
    bitsfi
    syl
    @5
    cn0
    elfpw
    sylanbrc
    #
    vk
    @5
    @7
    @15
    @0
    @8
    @6
    @5
    wceq
    @7
    @6
    @14
    vm
    csu
    @15
    @6
    @3
    @14
    vn
    vm
    @2
    @13
    c2
    cexp
    oveq2
    cbvsumv
    @6
    @5
    @14
    vm
    sumeq1
    syl5eq
    @8
    eqid
    #
    @5
    @14
    vm
    sumex
    fvmpt
    syl
    vk
    cA
    @7
    @4
    @0
    @8
    @6
    cA
    @3
    vn
    sumeq1
    @26
    cA
    @3
    vn
    sumex
    fvmpt
    3eqtr4d
    @1
    @0
    cn0
    @8
    wf1
    #
    @22
    @1
    @11
    @12
    wb
    @0
    cn0
    @8
    wf1o
    @27
    @1
    vk
    vn
    @8
    @26
    ackbijnn
    @0
    cn0
    @8
    f1of1
    mp1i
    @25
    @1
    id
    @0
    cn0
    @5
    cA
    @8
    f1fveq
    syl12anc
    mpbid
end
