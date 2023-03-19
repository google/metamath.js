include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "0nnn.mm"
include "eleq1.mm"
include "mtbiri.mm"
include "necon2ai.mm"

theorem nnne0
  let cA: class A


  assert |- ( A e. NN -> A =/= 0 )

  proof
    cA
    cn
    wcel
    #
    cA
    cc0
    cA
    cc0
    wceq
    @0
    cc0
    cn
    wcel
    0nnn
    cA
    cc0
    cn
    eleq1
    mtbiri
    necon2ai
end
