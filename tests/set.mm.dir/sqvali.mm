include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "sqval.mm"
include "ax-mp.mm"

theorem sqvali
  let cA: class A
  assume sqval.1: |- A e. CC


  assert |- ( A ^ 2 ) = ( A x. A )

  proof
    cA
    cc
    wcel
    cA
    c2
    cexp
    co
    cA
    cA
    cmul
    co
    wceq
    sqval.1
    cA
    sqval
    ax-mp
end
