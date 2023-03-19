include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "pncan3oi.mm"
include "addcomli.mm"
include "oveq1i.mm"
include "eqtr3i.mm"

theorem mvlladdi
  let cA: class A
  let cB: class B
  let cC: class C
  assume mvlladdi.1: |- A e. CC
  assume mvlladdi.2: |- B e. CC
  assume mvlladdi.3: |- ( A + B ) = C


  assert |- B = ( C - A )

  proof
    cB
    cA
    caddc
    co
    #
    cA
    cmin
    co
    cB
    cC
    cA
    cmin
    co
    cB
    cA
    mvlladdi.2
    mvlladdi.1
    pncan3oi
    @0
    cC
    cA
    cmin
    cA
    cB
    cC
    mvlladdi.1
    mvlladdi.2
    mvlladdi.3
    addcomli
    oveq1i
    eqtr3i
end
