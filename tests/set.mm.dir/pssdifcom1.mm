include "wss.mm"
include "wa.mm"
include "cdif.mm"
include "wn.mm"
include "wpss.mm"
include "wb.mm"
include "difcom.mm"
include "a1i.mm"
include "ssconb.mm"
include "ancoms.mm"
include "notbid.mm"
include "anbi12d.mm"
include "dfpss3.mm"
include "3bitr4g.mm"

theorem pssdifcom1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ C /\ B C_ C ) -> ( ( C \ A ) C. B <-> ( C \ B ) C. A ) )

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
    cC
    cA
    cdif
    #
    cB
    wss
    #
    cB
    @3
    wss
    #
    wn
    #
    wa
    cC
    cB
    cdif
    #
    cA
    wss
    #
    cA
    @7
    wss
    #
    wn
    #
    wa
    @3
    cB
    wpss
    @7
    cA
    wpss
    @2
    @4
    @8
    @6
    @10
    @4
    @8
    wb
    @2
    cC
    cA
    cB
    difcom
    a1i
    @2
    @5
    @9
    @1
    @0
    @5
    @9
    wb
    cB
    cA
    cC
    ssconb
    ancoms
    notbid
    anbi12d
    @3
    cB
    dfpss3
    @7
    cA
    dfpss3
    3bitr4g
end
