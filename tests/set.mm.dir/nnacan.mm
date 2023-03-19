include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "coa.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "wb.mm"
include "nnaword.mm"
include "3comr.mm"
include "3com13.mm"
include "anbi12d.mm"
include "bicomd.mm"
include "eqss.mm"
include "3bitr4g.mm"

theorem nnacan
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. _om /\ B e. _om /\ C e. _om ) -> ( ( A +o B ) = ( A +o C ) <-> B = C ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cC
    com
    wcel
    #
    w3a
    #
    cA
    cB
    coa
    co
    #
    cA
    cC
    coa
    co
    #
    wss
    #
    @5
    @4
    wss
    #
    wa
    #
    cB
    cC
    wss
    #
    cC
    cB
    wss
    #
    wa
    #
    @4
    @5
    wceq
    cB
    cC
    wceq
    @3
    @11
    @8
    @3
    @9
    @6
    @10
    @7
    @1
    @2
    @0
    @9
    @6
    wb
    cB
    cC
    cA
    nnaword
    3comr
    @2
    @1
    @0
    @10
    @7
    wb
    cC
    cB
    cA
    nnaword
    3com13
    anbi12d
    bicomd
    @4
    @5
    eqss
    cB
    cC
    eqss
    3bitr4g
end
