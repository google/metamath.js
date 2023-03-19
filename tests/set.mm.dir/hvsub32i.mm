include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "wceq.mm"
include "hvsub32.mm"
include "mp3an.mm"

theorem hvsub32i
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvass.1: |- A e. ~H
  assume hvass.2: |- B e. ~H
  assume hvass.3: |- C e. ~H


  assert |- ( ( A -h B ) -h C ) = ( ( A -h C ) -h B )

  proof
    cA
    chil
    wcel
    cB
    chil
    wcel
    cC
    chil
    wcel
    cA
    cB
    cmv
    co
    cC
    cmv
    co
    cA
    cC
    cmv
    co
    cB
    cmv
    co
    wceq
    hvass.1
    hvass.2
    hvass.3
    cA
    cB
    cC
    hvsub32
    mp3an
end
