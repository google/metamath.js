include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "divcan4.mm"
include "mp3an12.mm"

theorem divcan4zi
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC


  assert |- ( B =/= 0 -> ( ( A x. B ) / B ) = A )

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
    cmul
    co
    cB
    cdiv
    co
    cA
    wceq
    divclz.1
    divclz.2
    cA
    cB
    divcan4
    mp3an12
end
