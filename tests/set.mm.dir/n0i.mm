include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "con2i.mm"

theorem n0i
  let cA: class A
  let cB: class B


  assert |- ( B e. A -> -. A = (/) )

  proof
    cA
    c0
    wceq
    #
    cB
    cA
    wcel
    #
    @0
    @1
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
    con2i
end
