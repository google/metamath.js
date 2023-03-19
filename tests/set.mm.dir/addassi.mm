include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "addass.mm"
include "mp3an.mm"

theorem addassi
  let cA: class A
  let cB: class B
  let cC: class C
  assume axi.1: |- A e. CC
  assume axi.2: |- B e. CC
  assume axi.3: |- C e. CC


  assert |- ( ( A + B ) + C ) = ( A + ( B + C ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cA
    cB
    caddc
    co
    cC
    caddc
    co
    cA
    cB
    cC
    caddc
    co
    caddc
    co
    wceq
    axi.1
    axi.2
    axi.3
    cA
    cB
    cC
    addass
    mp3an
end
