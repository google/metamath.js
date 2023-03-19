include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "adddir.mm"
include "mp3an.mm"

theorem adddiri
  let cA: class A
  let cB: class B
  let cC: class C
  assume axi.1: |- A e. CC
  assume axi.2: |- B e. CC
  assume axi.3: |- C e. CC


  assert |- ( ( A + B ) x. C ) = ( ( A x. C ) + ( B x. C ) )

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
    cmul
    co
    cA
    cC
    cmul
    co
    cB
    cC
    cmul
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
    adddir
    mp3an
end
