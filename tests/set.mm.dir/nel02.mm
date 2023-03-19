include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"

theorem nel02
  let cA: class A
  let cB: class B


  assert |- ( A = (/) -> -. B e. A )

  proof
    cA
    c0
    wceq
    cB
    cA
    wcel
    cB
    c0
    wcel
    cB
    noel
    cA
    c0
    cB
    eleq2
    mtbiri
end
