include "wcel.mm"
include "wa.mm"
include "cpr.mm"
include "cpw.mm"
include "prelpw.mm"
include "ibi.mm"

theorem prelpwi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. C /\ B e. C ) -> { A , B } e. ~P C )

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
    cpw
    wcel
    cA
    cB
    cC
    cC
    cC
    prelpw
    ibi
end
