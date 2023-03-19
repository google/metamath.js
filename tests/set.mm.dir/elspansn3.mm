include "csh.mm"
include "wcel.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "wa.mm"
include "spansnss.mm"
include "sseld.mm"
include "3impia.mm"

theorem elspansn3
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. SH /\ B e. A /\ C e. ( span ` { B } ) ) -> C e. A )

  proof
    cA
    csh
    wcel
    #
    cB
    cA
    wcel
    #
    cC
    cB
    csn
    cspn
    cfv
    #
    wcel
    cC
    cA
    wcel
    @0
    @1
    wa
    @2
    cA
    cC
    cA
    cB
    spansnss
    sseld
    3impia
end
