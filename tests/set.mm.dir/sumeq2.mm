include "wceq.mm"
include "wral.mm"
include "cid.mm"
include "cfv.mm"
include "csu.mm"
include "fveq2.mm"
include "ralimi.mm"
include "sumeq2ii.mm"
include "syl.mm"

theorem sumeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k

  disjoint A k
  assert |- ( A. k e. A B = C -> sum_ k e. A B = sum_ k e. A C )

  proof
    cB
    cC
    wceq
    #
    vk
    cA
    wral
    cB
    cid
    cfv
    cC
    cid
    cfv
    wceq
    #
    vk
    cA
    wral
    cA
    cB
    vk
    csu
    cA
    cC
    vk
    csu
    wceq
    @0
    @1
    vk
    cA
    cB
    cC
    cid
    fveq2
    ralimi
    cA
    cB
    cC
    vk
    sumeq2ii
    syl
end
