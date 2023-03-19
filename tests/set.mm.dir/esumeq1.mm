include "wceq.mm"
include "id.mm"
include "eqidd.mm"
include "esumeq12d.mm"

theorem esumeq1
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k

  disjoint A k
  disjoint B k
  assert |- ( A = B -> sum* k e. A C = sum* k e. B C )

  proof
    cA
    cB
    wceq
    #
    cA
    cB
    cC
    cC
    vk
    @0
    id
    @0
    cC
    eqidd
    esumeq12d
end
