include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "divcan3.mm"
include "mp3an12.mm"

theorem divcan3zi
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC


  assert |- ( B =/= 0 -> ( ( B x. A ) / B ) = A )

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
    cB
    cA
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
    divcan3
    mp3an12
end
