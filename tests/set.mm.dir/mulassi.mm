include "cc.mm"
include "wcel.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulass.mm"
include "mp3an.mm"

theorem mulassi
  let cA: class A
  let cB: class B
  let cC: class C
  assume axi.1: |- A e. CC
  assume axi.2: |- B e. CC
  assume axi.3: |- C e. CC


  assert |- ( ( A x. B ) x. C ) = ( A x. ( B x. C ) )

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
    cmul
    co
    cC
    cmul
    co
    cA
    cB
    cC
    cmul
    co
    cmul
    co
    wceq
    axi.1
    axi.2
    axi.3
    cA
    cB
    cC
    mulass
    mp3an
end
