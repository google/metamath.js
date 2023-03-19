include "chil.mm"
include "wcel.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "hvadd32.mm"
include "mp3an.mm"

theorem hvadd32i
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvass.1: |- A e. ~H
  assume hvass.2: |- B e. ~H
  assume hvass.3: |- C e. ~H


  assert |- ( ( A +h B ) +h C ) = ( ( A +h C ) +h B )

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
    cva
    co
    cC
    cva
    co
    cA
    cC
    cva
    co
    cB
    cva
    co
    wceq
    hvass.1
    hvass.2
    hvass.3
    cA
    cB
    cC
    hvadd32
    mp3an
end
