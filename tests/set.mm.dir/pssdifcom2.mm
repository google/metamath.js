include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "wn.mm"
include "wpss.mm"
include "wb.mm"
include "ssconb.mm"
include "ancoms.mm"
include "difcom.mm"
include "notbii.mm"
include "a1i.mm"
include "anbi12d.mm"
include "dfpss3.mm"
include "3bitr4g.mm"

theorem pssdifcom2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ C /\ B C_ C ) -> ( B C. ( C \ A ) <-> A C. ( C \ B ) ) )

  proof
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wa
    #
    cB
    cC
    cA
    cdif
    #
    wss
    #
    @3
    cB
    wss
    #
    wn
    #
    wa
    cA
    cC
    cB
    cdif
    #
    wss
    #
    @7
    cA
    wss
    #
    wn
    #
    wa
    cB
    @3
    wpss
    cA
    @7
    wpss
    @2
    @4
    @8
    @6
    @10
    @1
    @0
    @4
    @8
    wb
    cB
    cA
    cC
    ssconb
    ancoms
    @6
    @10
    wb
    @2
    @5
    @9
    cC
    cA
    cB
    difcom
    notbii
    a1i
    anbi12d
    cB
    @3
    dfpss3
    cA
    @7
    dfpss3
    3bitr4g
end
