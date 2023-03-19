include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "divcan4i.mm"
include "mulcomli.mm"
include "oveq1i.mm"
include "eqtr3i.mm"

theorem mvllmuli
  let cA: class A
  let cB: class B
  let cC: class C
  assume mvllmuli.1: |- A e. CC
  assume mvllmuli.2: |- B e. CC
  assume mvllmuli.3: |- A =/= 0
  assume mvllmuli.4: |- ( A x. B ) = C


  assert |- B = ( C / A )

  proof
    cB
    cA
    cmul
    co
    #
    cA
    cdiv
    co
    cB
    cC
    cA
    cdiv
    co
    cB
    cA
    mvllmuli.2
    mvllmuli.1
    mvllmuli.3
    divcan4i
    @0
    cC
    cA
    cdiv
    cA
    cB
    cC
    mvllmuli.1
    mvllmuli.2
    mvllmuli.4
    mulcomli
    oveq1i
    eqtr3i
end
