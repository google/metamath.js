include "cva.mm"
include "co.mm"
include "hvcomi.mm"
include "oveq1i.mm"
include "hvassi.mm"
include "3eqtr3i.mm"

theorem hvadd12i
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvass.1: |- A e. ~H
  assume hvass.2: |- B e. ~H
  assume hvass.3: |- C e. ~H


  assert |- ( A +h ( B +h C ) ) = ( B +h ( A +h C ) )

  proof
    cA
    cB
    cva
    co
    #
    cC
    cva
    co
    cB
    cA
    cva
    co
    #
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
    cB
    cA
    cC
    cva
    co
    cva
    co
    @0
    @1
    cC
    cva
    cA
    cB
    hvass.1
    hvass.2
    hvcomi
    oveq1i
    cA
    cB
    cC
    hvass.1
    hvass.2
    hvass.3
    hvassi
    cB
    cA
    cC
    hvass.2
    hvass.1
    hvass.3
    hvassi
    3eqtr3i
end
