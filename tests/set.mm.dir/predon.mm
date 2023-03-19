include "con0.mm"
include "wcel.mm"
include "cep.mm"
include "cpred.mm"
include "cin.mm"
include "predep.mm"
include "wss.mm"
include "wceq.mm"
include "onss.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqtrd.mm"

theorem predon
  let cA: class A


  assert |- ( A e. On -> Pred ( _E , On , A ) = A )

  proof
    cA
    con0
    wcel
    #
    con0
    cep
    cA
    cpred
    con0
    cA
    cin
    #
    cA
    con0
    con0
    cA
    predep
    @0
    cA
    con0
    wss
    @1
    cA
    wceq
    cA
    onss
    cA
    con0
    sseqin2
    sylib
    eqtrd
end
