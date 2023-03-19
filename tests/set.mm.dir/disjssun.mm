include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cun.mm"
include "wss.mm"
include "uneq2.mm"
include "indi.mm"
include "equncomi.mm"
include "un0.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"
include "eqeq1d.mm"
include "df-ss.mm"
include "3bitr4g.mm"

theorem disjssun
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( A i^i B ) = (/) -> ( A C_ ( B u. C ) <-> A C_ C ) )

  proof
    cA
    cB
    cin
    #
    c0
    wceq
    #
    cA
    cB
    cC
    cun
    #
    cin
    #
    cA
    wceq
    cA
    cC
    cin
    #
    cA
    wceq
    cA
    @2
    wss
    cA
    cC
    wss
    @1
    @3
    @4
    cA
    @1
    @4
    @0
    cun
    @4
    c0
    cun
    #
    @3
    @4
    @0
    c0
    @4
    uneq2
    @3
    @0
    @4
    cA
    cB
    cC
    indi
    equncomi
    @5
    @4
    @4
    un0
    eqcomi
    3eqtr4g
    eqeq1d
    cA
    @2
    df-ss
    cA
    cC
    df-ss
    3bitr4g
end
