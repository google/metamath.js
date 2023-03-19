include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "add12.mm"
include "mp3an.mm"

theorem add12i
  let cA: class A
  let cB: class B
  let cC: class C
  assume add.1: |- A e. CC
  assume add.2: |- B e. CC
  assume add.3: |- C e. CC


  assert |- ( A + ( B + C ) ) = ( B + ( A + C ) )

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
    cC
    caddc
    co
    caddc
    co
    cB
    cA
    cC
    caddc
    co
    caddc
    co
    wceq
    add.1
    add.2
    add.3
    cA
    cB
    cC
    add12
    mp3an
end
