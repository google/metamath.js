include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "divdiv32.mm"
include "mp3an1.mm"
include "mpanr1.mm"
include "mpanl1.mm"

theorem divdiv23zi
  let cA: class A
  let cB: class B
  let cC: class C
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC


  assert |- ( ( B =/= 0 /\ C =/= 0 ) -> ( ( A / B ) / C ) = ( ( A / C ) / B ) )

  proof
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    cC
    cc0
    wne
    #
    cA
    cB
    cdiv
    co
    cC
    cdiv
    co
    cA
    cC
    cdiv
    co
    cB
    cdiv
    co
    wceq
    #
    divclz.2
    @0
    @1
    wa
    #
    cC
    cc
    wcel
    #
    @2
    @3
    divmulz.3
    cA
    cc
    wcel
    @4
    @5
    @2
    wa
    @3
    divclz.1
    cA
    cB
    cC
    divdiv32
    mp3an1
    mpanr1
    mpanl1
end
