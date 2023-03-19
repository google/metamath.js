include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "mulcomi.mm"
include "oveq1i.mm"
include "divmuldivi.mm"
include "3eqtr4ri.mm"

theorem divmul13i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume divclz.1: |- A e. CC
  assume divclz.2: |- B e. CC
  assume divmulz.3: |- C e. CC
  assume divmuldiv.4: |- D e. CC
  assume divmuldiv.5: |- B =/= 0
  assume divmuldiv.6: |- D =/= 0


  assert |- ( ( A / B ) x. ( C / D ) ) = ( ( C / B ) x. ( A / D ) )

  proof
    cC
    cA
    cmul
    co
    #
    cB
    cD
    cmul
    co
    #
    cdiv
    co
    cA
    cC
    cmul
    co
    #
    @1
    cdiv
    co
    cC
    cB
    cdiv
    co
    cA
    cD
    cdiv
    co
    cmul
    co
    cA
    cB
    cdiv
    co
    cC
    cD
    cdiv
    co
    cmul
    co
    @0
    @2
    @1
    cdiv
    cC
    cA
    divmulz.3
    divclz.1
    mulcomi
    oveq1i
    cC
    cB
    cA
    cD
    divmulz.3
    divclz.2
    divclz.1
    divmuldiv.4
    divmuldiv.5
    divmuldiv.6
    divmuldivi
    cA
    cB
    cC
    cD
    divclz.1
    divclz.2
    divmulz.3
    divmuldiv.4
    divmuldiv.5
    divmuldiv.6
    divmuldivi
    3eqtr4ri
end
