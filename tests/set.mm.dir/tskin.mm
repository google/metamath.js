include "ctsk.mm"
include "wcel.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "tskss.mm"
include "mp3an3.mm"

theorem tskin
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( T e. Tarski /\ A e. T ) -> ( A i^i B ) e. T )

  proof
    cT
    ctsk
    wcel
    cA
    cT
    wcel
    cA
    cB
    cin
    #
    cA
    wss
    @0
    cT
    wcel
    cA
    cB
    inss1
    cA
    @0
    cT
    tskss
    mp3an3
end
