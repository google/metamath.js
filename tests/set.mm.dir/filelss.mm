include "cfil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfbas.mm"
include "wss.mm"
include "filfbas.mm"
include "fbelss.mm"
include "sylan.mm"

theorem filelss
  let cA: class A
  let cF: class F
  let cX: class X


  assert |- ( ( F e. ( Fil ` X ) /\ A e. F ) -> A C_ X )

  proof
    cF
    cX
    cfil
    cfv
    wcel
    cF
    cX
    cfbas
    cfv
    wcel
    cA
    cF
    wcel
    cA
    cX
    wss
    cF
    cX
    filfbas
    cX
    cF
    cA
    fbelss
    sylan
end
