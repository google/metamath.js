include "cvv.mm"
include "wcel.mm"
include "cop.mm"
include "c1st.mm"
include "wbr.mm"
include "wceq.mm"
include "wb.mm"
include "br1steqg.mm"
include "mp2an.mm"

theorem br1steq
  let cA: class A
  let cB: class B
  let cC: class C
  assume br1steq.1: |- A e. _V
  assume br1steq.2: |- B e. _V


  assert |- ( <. A , B >. 1st C <-> C = A )

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
    c1st
    wbr
    cC
    cA
    wceq
    wb
    br1steq.1
    br1steq.2
    cA
    cB
    cC
    cvv
    cvv
    br1steqg
    mp2an
end
