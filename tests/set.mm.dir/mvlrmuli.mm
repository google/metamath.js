include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "divcan4i.mm"
include "oveq1i.mm"
include "eqtr3i.mm"

theorem mvlrmuli
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x
  assume mvlrmuli.1: |- A e. CC
  assume mvlrmuli.2: |- B e. CC
  assume mvlrmuli.3: |- B =/= 0
  assume mvlrmuli.4: |- ( A x. B ) = C


  assert |- A = ( C / B )

  proof
    cA
    cB
    cmul
    co
    #
    cB
    cdiv
    co
    cA
    cC
    cB
    cdiv
    co
    cA
    cB
    mvlrmuli.1
    mvlrmuli.2
    mvlrmuli.3
    divcan4i
    @0
    cC
    cB
    cdiv
    mvlrmuli.4
    oveq1i
    eqtr3i
end
