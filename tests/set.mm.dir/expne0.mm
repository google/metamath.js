include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "expeq0.mm"
include "necon3bid.mm"

theorem expne0
  let cA: class A
  let cN: class N


  assert |- ( ( A e. CC /\ N e. NN ) -> ( ( A ^ N ) =/= 0 <-> A =/= 0 ) )

  proof
    cA
    cc
    wcel
    cN
    cn
    wcel
    wa
    cA
    cN
    cexp
    co
    cc0
    cA
    cc0
    cA
    cN
    expeq0
    necon3bid
end
