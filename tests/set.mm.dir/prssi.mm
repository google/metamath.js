include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "wss.mm"
include "prssg.mm"
include "ibi.mm"

theorem prssi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. C /\ B e. C ) -> { A , B } C_ C )

  proof
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
    cA
    cB
    cC
    cC
    cC
    prssg
    ibi
end
