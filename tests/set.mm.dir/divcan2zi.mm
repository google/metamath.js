include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "divcan2.mm"
include "mp3an12.mm"

theorem divcan2zi
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC


  assert |- ( B =/= 0 -> ( B x. ( A / B ) ) = A )

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
    cB
    cdiv
    co
    cmul
    co
    cA
    wceq
    divclz.1
    divclz.2
    cA
    cB
    divcan2
    mp3an12
end
