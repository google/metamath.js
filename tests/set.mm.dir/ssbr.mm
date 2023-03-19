include "wss.mm"
include "id.mm"
include "ssbrd.mm"

theorem ssbr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ B -> ( C A D -> C B D ) )

  proof
    cA
    cB
    wss
    #
    cA
    cB
    cC
    cD
    @0
    id
    ssbrd
end
