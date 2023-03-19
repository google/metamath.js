include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "sqeq0.mm"
include "necon3bid.mm"

theorem sqne0
  let cA: class A


  assert |- ( A e. CC -> ( ( A ^ 2 ) =/= 0 <-> A =/= 0 ) )

  proof
    cA
    cc
    wcel
    cA
    c2
    cexp
    co
    cc0
    cA
    cc0
    cA
    sqeq0
    necon3bid
end
