include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "wa.mm"
include "divass.mm"
include "mp3an12.mm"
include "mpan.mm"

theorem divasszi
  let cA: class A
  let cB: class B
  let cC: class C
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC


  assert |- ( C =/= 0 -> ( ( A x. B ) / C ) = ( A x. ( B / C ) ) )

  proof
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    cA
    cB
    cmul
    co
    cC
    cdiv
    co
    cA
    cB
    cC
    cdiv
    co
    cmul
    co
    wceq
    #
    divmulz.3
    cA
    cc
    wcel
    cB
    cc
    wcel
    @0
    @1
    wa
    @2
    divclz.1
    divclz.2
    cA
    cB
    cC
    divass
    mp3an12
    mpan
end
