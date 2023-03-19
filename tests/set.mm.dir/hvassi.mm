include "chil.mm"
include "wcel.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "ax-hvass.mm"
include "mp3an.mm"

theorem hvassi
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvass.1: |- A e. ~H
  assume hvass.2: |- B e. ~H
  assume hvass.3: |- C e. ~H


  assert |- ( ( A +h B ) +h C ) = ( A +h ( B +h C ) )

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
    cB
    cC
    cva
    co
    cva
    co
    wceq
    hvass.1
    hvass.2
    hvass.3
    cA
    cB
    cC
    ax-hvass
    mp3an
end
