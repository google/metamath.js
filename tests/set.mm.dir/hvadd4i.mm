include "chil.mm"
include "wcel.mm"
include "cva.mm"
include "co.mm"
include "wceq.mm"
include "hvadd4.mm"
include "mp4an.mm"

theorem hvadd4i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume hvass.1: |- A e. ~H
  assume hvass.2: |- B e. ~H
  assume hvass.3: |- C e. ~H
  assume hvadd4.4: |- D e. ~H


  assert |- ( ( A +h B ) +h ( C +h D ) ) = ( ( A +h C ) +h ( B +h D ) )

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
    cD
    chil
    wcel
    cA
    cB
    cva
    co
    cC
    cD
    cva
    co
    cva
    co
    cA
    cC
    cva
    co
    cB
    cD
    cva
    co
    cva
    co
    wceq
    hvass.1
    hvass.2
    hvass.3
    hvadd4.4
    cA
    cB
    cC
    cD
    hvadd4
    mp4an
end
