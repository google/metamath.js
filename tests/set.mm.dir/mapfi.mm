include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "xpfi.mm"
include "ancoms.mm"
include "pwfi.mm"
include "sylib.mm"
include "mapsspw.mm"
include "ssfi.mm"
include "sylancl.mm"

theorem mapfi
  let cA: class A
  let cB: class B


  assert |- ( ( A e. Fin /\ B e. Fin ) -> ( A ^m B ) e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cB
    cfn
    wcel
    #
    wa
    #
    cB
    cA
    cxp
    #
    cpw
    #
    cfn
    wcel
    #
    cA
    cB
    cmap
    co
    #
    @4
    wss
    @6
    cfn
    wcel
    @2
    @3
    cfn
    wcel
    #
    @5
    @1
    @0
    @7
    cB
    cA
    xpfi
    ancoms
    @3
    pwfi
    sylib
    cA
    cB
    mapsspw
    @4
    @6
    ssfi
    sylancl
end
