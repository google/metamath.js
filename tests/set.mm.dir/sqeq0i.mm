include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "sqeq0.mm"
include "ax-mp.mm"

theorem sqeq0i
  let cA: class A
  assume sqval.1: |- A e. CC


  assert |- ( ( A ^ 2 ) = 0 <-> A = 0 )

  proof
    cA
    cc
    wcel
    cA
    c2
    cexp
    co
    cc0
    wceq
    cA
    cc0
    wceq
    wb
    sqval.1
    cA
    sqeq0
    ax-mp
end
