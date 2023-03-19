include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "elin.mm"
include "elpwg.mm"
include "pm5.32ri.mm"
include "bitri.mm"

theorem elfpw
  let cA: class A
  let cB: class B


  assert |- ( A e. ( ~P B i^i Fin ) <-> ( A C_ B /\ A e. Fin ) )

  proof
    cA
    cB
    cpw
    #
    cfn
    cin
    wcel
    cA
    @0
    wcel
    #
    cA
    cfn
    wcel
    #
    wa
    cA
    cB
    wss
    #
    @2
    wa
    cA
    @0
    cfn
    elin
    @2
    @1
    @3
    cA
    cB
    cfn
    elpwg
    pm5.32ri
    bitri
end
