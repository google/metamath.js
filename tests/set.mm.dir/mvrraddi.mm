include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "oveq1i.mm"
include "pncan3oi.mm"
include "eqtri.mm"

theorem mvrraddi
  let cA: class A
  let cB: class B
  let cC: class C
  assume mvrraddi.1: |- B e. CC
  assume mvrraddi.2: |- C e. CC
  assume mvrraddi.3: |- A = ( B + C )


  assert |- ( A - C ) = B

  proof
    cA
    cC
    cmin
    co
    cB
    cC
    caddc
    co
    #
    cC
    cmin
    co
    cB
    cA
    @0
    cC
    cmin
    mvrraddi.3
    oveq1i
    cB
    cC
    mvrraddi.1
    mvrraddi.2
    pncan3oi
    eqtri
end
