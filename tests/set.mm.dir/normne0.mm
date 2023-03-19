include "chil.mm"
include "wcel.mm"
include "cno.mm"
include "cfv.mm"
include "cc0.mm"
include "c0v.mm"
include "norm-i.mm"
include "necon3bid.mm"

theorem normne0
  let cA: class A


  assert |- ( A e. ~H -> ( ( normh ` A ) =/= 0 <-> A =/= 0h ) )

  proof
    cA
    chil
    wcel
    cA
    cno
    cfv
    cc0
    cA
    c0v
    cA
    norm-i
    necon3bid
end
