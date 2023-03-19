include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "csu.mm"
include "cid.mm"
include "eqid.mm"
include "fvmpt2i.mm"
include "sumeq2i.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "fveq2.mm"
include "cbvsumi.mm"
include "sum2id.mm"
include "3eqtr4i.mm"

theorem sumfc
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  assert |- sum_ j e. A ( ( k e. A |-> B ) ` j ) = sum_ k e. A B

  proof
    cA
    vk
    cv
    #
    vk
    cA
    cB
    cmpt
    #
    cfv
    #
    vk
    csu
    cA
    cB
    cid
    cfv
    #
    vk
    csu
    cA
    vj
    cv
    #
    @1
    cfv
    #
    vj
    csu
    cA
    cB
    vk
    csu
    cA
    @2
    @3
    vk
    vk
    cA
    cB
    @1
    @1
    eqid
    fvmpt2i
    sumeq2i
    cA
    @5
    @2
    vj
    vk
    vk
    cA
    cB
    @4
    nffvmpt1
    vj
    @2
    nfcv
    @4
    @0
    @1
    fveq2
    cbvsumi
    cA
    cB
    vk
    sum2id
    3eqtr4i
end
