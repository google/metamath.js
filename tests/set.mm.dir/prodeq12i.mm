include "cprod.mm"
include "prodeq2i.mm"
include "prodeq1i.mm"
include "eqtri.mm"

theorem prodeq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  assume prodeq12i.1: |- A = B
  assume prodeq12i.2: |- ( k e. A -> C = D )

  disjoint A k
  disjoint B k
  assert |- prod_ k e. A C = prod_ k e. B D

  proof
    cA
    cC
    vk
    cprod
    cA
    cD
    vk
    cprod
    cB
    cD
    vk
    cprod
    cA
    cC
    cD
    vk
    prodeq12i.2
    prodeq2i
    cA
    cB
    cD
    vk
    prodeq12i.1
    prodeq1i
    eqtri
end
