include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cmul.mm"
include "wceq.mm"
include "divrec.mm"
include "mp3an12.mm"

theorem divreczi
  let cA: class A
  let cB: class B
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC


  assert |- ( B =/= 0 -> ( A / B ) = ( A x. ( 1 / B ) ) )

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
    cA
    c1
    cB
    cdiv
    co
    cmul
    co
    wceq
    divclz.1
    divclz.2
    cA
    cB
    divrec
    mp3an12
end
