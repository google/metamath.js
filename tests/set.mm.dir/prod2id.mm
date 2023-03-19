include "cid.mm"
include "cfv.mm"
include "wceq.mm"
include "cprod.mm"
include "prodeq2ii.mm"
include "cv.mm"
include "wcel.mm"
include "cvv.mm"
include "fvex.mm"
include "fvi.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "a1i.mm"
include "mprg.mm"

theorem prod2id
  let cA: class A
  let cB: class B
  let vk: setvar k

  disjoint A k
  assert |- prod_ k e. A B = prod_ k e. A ( _I ` B )

  proof
    cB
    cid
    cfv
    #
    @0
    cid
    cfv
    #
    wceq
    #
    cA
    cB
    vk
    cprod
    cA
    @0
    vk
    cprod
    wceq
    vk
    cA
    cA
    cB
    @0
    vk
    prodeq2ii
    @2
    vk
    cv
    cA
    wcel
    @1
    @0
    @0
    cvv
    wcel
    @1
    @0
    wceq
    cB
    cid
    fvex
    @0
    cvv
    fvi
    ax-mp
    eqcomi
    a1i
    mprg
end
