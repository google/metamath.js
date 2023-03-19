include "wceq.mm"
include "neneqd.mm"
include "necon2ai.mm"

theorem necon2i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume necon2i.1: |- ( A = B -> C =/= D )


  assert |- ( C = D -> A =/= B )

  proof
    cC
    cD
    wceq
    cA
    cB
    cA
    cB
    wceq
    cC
    cD
    necon2i.1
    neneqd
    necon2ai
end
