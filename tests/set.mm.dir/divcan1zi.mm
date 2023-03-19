include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "divcan1.mm"
include "mp3an12.mm"

theorem divcan1zi
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC


  assert |- ( B =/= 0 -> ( ( A / B ) x. B ) = A )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    cB
    cmul
    co
    cA
    wceq
    divclz.1
    divclz.2
    cA
    cB
    divcan1
    mp3an12
end
