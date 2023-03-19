include "wpss.mm"
include "wo.mm"
include "wceq.mm"
include "wss.mm"
include "w3o.mm"
include "or32.mm"
include "sspss.mm"
include "eqcom.mm"
include "orbi2i.mm"
include "bitri.mm"
include "orbi12i.mm"
include "orordir.mm"
include "bitr4i.mm"
include "df-3or.mm"
include "3bitr4i.mm"

theorem sspsstri
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ B \/ B C_ A ) <-> ( A C. B \/ A = B \/ B C. A ) )

  proof
    cA
    cB
    wpss
    #
    cB
    cA
    wpss
    #
    wo
    cA
    cB
    wceq
    #
    wo
    #
    @0
    @2
    wo
    #
    @1
    wo
    cA
    cB
    wss
    #
    cB
    cA
    wss
    #
    wo
    #
    @0
    @2
    @1
    w3o
    @0
    @1
    @2
    or32
    @7
    @4
    @1
    @2
    wo
    #
    wo
    @3
    @5
    @4
    @6
    @8
    cA
    cB
    sspss
    @6
    @1
    cB
    cA
    wceq
    #
    wo
    @8
    cB
    cA
    sspss
    @9
    @2
    @1
    cB
    cA
    eqcom
    orbi2i
    bitri
    orbi12i
    @0
    @1
    @2
    orordir
    bitr4i
    @0
    @2
    @1
    df-3or
    3bitr4i
end
