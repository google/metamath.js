include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "wa.mm"
include "divdir.mm"
include "mp3an12.mm"
include "mpan.mm"

theorem divdirzi
  let cA: class A
  let cB: class B
  let cC: class C
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC


  assert |- ( C =/= 0 -> ( ( A + B ) / C ) = ( ( A / C ) + ( B / C ) ) )

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
    caddc
    co
    cC
    cdiv
    co
    cA
    cC
    cdiv
    co
    cB
    cC
    cdiv
    co
    caddc
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
    divdir
    mp3an12
    mpan
end
