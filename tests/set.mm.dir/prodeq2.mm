include "wceq.mm"
include "wral.mm"
include "cid.mm"
include "cfv.mm"
include "cprod.mm"
include "fveq2.mm"
include "ralimi.mm"
include "prodeq2ii.mm"
include "syl.mm"

theorem prodeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k

  disjoint A k
  assert |- ( A. k e. A B = C -> prod_ k e. A B = prod_ k e. A C )

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
    cprod
    cA
    cC
    vk
    cprod
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
    prodeq2ii
    syl
end
