include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "comraddi.mm"
include "oveq1i.mm"
include "pncan3oi.mm"
include "eqtri.mm"

theorem mvrladdi
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x
  assume mvrladdi.1: |- B e. CC
  assume mvrladdi.2: |- C e. CC
  assume mvrladdi.3: |- A = ( B + C )


  assert |- ( A - B ) = C

  proof
    cA
    cB
    cmin
    co
    cC
    cB
    caddc
    co
    #
    cB
    cmin
    co
    cC
    cA
    @0
    cB
    cmin
    cA
    cB
    cC
    mvrladdi.1
    mvrladdi.2
    mvrladdi.3
    comraddi
    oveq1i
    cC
    cB
    mvrladdi.2
    mvrladdi.1
    pncan3oi
    eqtri
end
