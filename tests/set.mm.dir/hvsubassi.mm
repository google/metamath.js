include "chil.mm"
include "wcel.mm"
include "cmv.mm"
include "co.mm"
include "cva.mm"
include "wceq.mm"
include "hvsubass.mm"
include "mp3an.mm"

theorem hvsubassi
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvass.1: |- A e. ~H
  assume hvass.2: |- B e. ~H
  assume hvass.3: |- C e. ~H


  assert |- ( ( A -h B ) -h C ) = ( A -h ( B +h C ) )

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
    cB
    cC
    cva
    co
    cmv
    co
    wceq
    hvass.1
    hvass.2
    hvass.3
    cA
    cB
    cC
    hvsubass
    mp3an
end
