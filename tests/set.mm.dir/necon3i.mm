include "wne.mm"
include "wceq.mm"
include "necon3ai.mm"
include "neqned.mm"

theorem necon3i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume necon3i.1: |- ( A = B -> C = D )


  assert |- ( C =/= D -> A =/= B )

  proof
    cC
    cD
    wne
    cA
    cB
    cA
    cB
    wceq
    cC
    cD
    necon3i.1
    necon3ai
    neqned
end
