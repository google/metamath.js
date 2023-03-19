include "wceq.mm"
include "wne.mm"
include "neneqd.mm"
include "necon4ai.mm"

theorem necon4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume necon4i.1: |- ( A =/= B -> C =/= D )


  assert |- ( C = D -> A = B )

  proof
    cC
    cD
    wceq
    cA
    cB
    cA
    cB
    wne
    cC
    cD
    necon4i.1
    neneqd
    necon4ai
end
