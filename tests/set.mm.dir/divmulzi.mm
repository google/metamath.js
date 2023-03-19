include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "wb.mm"
include "wa.mm"
include "divmul.mm"
include "mp3an12.mm"
include "mpan.mm"

theorem divmulzi
  let cA: class A
  let cB: class B
  let cC: class C
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC


  assert |- ( B =/= 0 -> ( ( A / B ) = C <-> ( B x. C ) = A ) )

  proof
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cA
    cB
    cdiv
    co
    cC
    wceq
    cB
    cC
    cmul
    co
    cA
    wceq
    wb
    #
    divclz.2
    cA
    cc
    wcel
    cC
    cc
    wcel
    @0
    @1
    wa
    @2
    divclz.1
    divmulz.3
    cA
    cC
    cB
    divmul
    mp3an12
    mpan
end
