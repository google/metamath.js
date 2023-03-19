include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "pncan3oi.mm"
include "oveq1i.mm"
include "eqtr3i.mm"

theorem mvlraddi
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x
  assume mvlraddi.1: |- A e. CC
  assume mvlraddi.2: |- B e. CC
  assume mvlraddi.3: |- ( A + B ) = C


  assert |- A = ( C - B )

  proof
    cA
    cB
    caddc
    co
    #
    cB
    cmin
    co
    cA
    cC
    cB
    cmin
    co
    cA
    cB
    mvlraddi.1
    mvlraddi.2
    pncan3oi
    @0
    cC
    cB
    cmin
    mvlraddi.3
    oveq1i
    eqtr3i
end
