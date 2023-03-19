include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "mulneg1.mm"
include "mulneg2.mm"
include "eqtr4d.mm"

theorem mulneg12
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC ) -> ( -u A x. B ) = ( A x. -u B ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    wa
    cA
    cneg
    cB
    cmul
    co
    cA
    cB
    cmul
    co
    cneg
    cA
    cB
    cneg
    cmul
    co
    cA
    cB
    mulneg1
    cA
    cB
    mulneg2
    eqtr4d
end
