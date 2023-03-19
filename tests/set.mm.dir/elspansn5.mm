include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wn.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "wa.mm"
include "c0v.mm"
include "wceq.mm"
include "wi.mm"
include "wne.mm"
include "elspansn4.mm"
include "biimprd.mm"
include "exp32.mm"
include "com34.mm"
include "imp32.mm"
include "necon1bd.mm"
include "exp31.mm"
include "imp4c.mm"

theorem elspansn5
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. SH -> ( ( ( B e. ~H /\ -. B e. A ) /\ ( C e. ( span ` { B } ) /\ C e. A ) ) -> C = 0h ) )

  proof
    cA
    csh
    wcel
    #
    cB
    chil
    wcel
    #
    cB
    cA
    wcel
    #
    wn
    #
    cC
    cB
    csn
    cspn
    cfv
    wcel
    #
    cC
    cA
    wcel
    #
    wa
    #
    cC
    c0v
    wceq
    #
    @0
    @1
    @6
    @3
    @7
    @0
    @1
    @6
    @3
    @7
    wi
    @0
    @1
    wa
    #
    @6
    wa
    @2
    cC
    c0v
    @8
    @4
    @5
    cC
    c0v
    wne
    #
    @2
    wi
    @8
    @4
    @9
    @5
    @2
    @8
    @4
    @9
    @5
    @2
    wi
    @8
    @4
    @9
    wa
    wa
    @2
    @5
    cA
    cB
    cC
    elspansn4
    biimprd
    exp32
    com34
    imp32
    necon1bd
    exp31
    com34
    imp4c
end
