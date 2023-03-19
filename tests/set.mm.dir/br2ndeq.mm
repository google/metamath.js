include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "c2nd.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "br2ndeqg.mm"
include "mp2an.mm"

theorem br2ndeq
  let cA: class A
  let cB: class B
  let cC: class C
  assume br1steq.1: |- A e. _V
  assume br1steq.2: |- B e. _V


  assert |- ( <. A , B >. 2nd C <-> C = B )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cop
    cC
    c2nd
    wbr
    cC
    cB
    wceq
    wb
    br1steq.1
    br1steq.2
    cA
    cB
    cC
    cvv
    cvv
    br2ndeqg
    mp2an
end
