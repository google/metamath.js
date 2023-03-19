include "cvv.mm"
include "wcel.mm"
include "cpr.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "wb.mm"
include "prsspwg.mm"
include "mp2an.mm"

theorem prsspw
  let cA: class A
  let cB: class B
  let cC: class C
  assume prsspw.1: |- A e. _V
  assume prsspw.2: |- B e. _V


  assert |- ( { A , B } C_ ~P C <-> ( A C_ C /\ B C_ C ) )

  proof
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    cpr
    cC
    cpw
    wss
    cA
    cC
    wss
    cB
    cC
    wss
    wa
    wb
    prsspw.1
    prsspw.2
    cA
    cB
    cC
    cvv
    cvv
    prsspwg
    mp2an
end
