include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wss.mm"
include "wb.mm"
include "prssg.mm"
include "mp2an.mm"

theorem prss
  let cA: class A
  let cB: class B
  let cC: class C
  assume prss.1: |- A e. _V
  assume prss.2: |- B e. _V


  assert |- ( ( A e. C /\ B e. C ) <-> { A , B } C_ C )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cC
    wcel
    cB
    cC
    wcel
    wa
    cA
    cB
    cpr
    cC
    wss
    wb
    prss.1
    prss.2
    cA
    cB
    cC
    cvv
    cvv
    prssg
    mp2an
end
