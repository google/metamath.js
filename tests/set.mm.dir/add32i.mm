include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "add32.mm"
include "mp3an.mm"

theorem add32i
  let cA: class A
  let cB: class B
  let cC: class C
  assume add.1: |- A e. CC
  assume add.2: |- B e. CC
  assume add.3: |- C e. CC


  assert |- ( ( A + B ) + C ) = ( ( A + C ) + B )

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
    cC
    caddc
    co
    cB
    caddc
    co
    wceq
    add.1
    add.2
    add.3
    cA
    cB
    cC
    add32
    mp3an
end
