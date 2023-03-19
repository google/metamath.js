include "cv.mm"
include "cmpt.mm"
include "cfv.mm"
include "cprod.mm"
include "cid.mm"
include "eqid.mm"
include "fvmpt2i.mm"
include "prodeq2i.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "fveq2.mm"
include "cbvprodi.mm"
include "prod2id.mm"
include "3eqtr4i.mm"

theorem prodfc
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint B j
  assert |- prod_ j e. A ( ( k e. A |-> B ) ` j ) = prod_ k e. A B

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
    cprod
    cA
    cB
    cid
    cfv
    #
    vk
    cprod
    cA
    vj
    cv
    #
    @1
    cfv
    #
    vj
    cprod
    cA
    cB
    vk
    cprod
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
    prodeq2i
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
    cbvprodi
    cA
    cB
    vk
    prod2id
    3eqtr4i
end
