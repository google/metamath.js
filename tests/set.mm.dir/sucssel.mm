include "wcel.mm"
include "csuc.mm"
include "wss.mm"
include "sucidg.mm"
include "ssel.mm"
include "syl5com.mm"

theorem sucssel
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( suc A C_ B -> A e. B ) )

  proof
    cA
    cV
    wcel
    cA
    cA
    csuc
    #
    wcel
    @0
    cB
    wss
    cA
    cB
    wcel
    cA
    cV
    sucidg
    @0
    cB
    cA
    ssel
    syl5com
end
