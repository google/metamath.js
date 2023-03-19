include "wpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "wbr.mm"
include "cid.mm"
include "cun.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "poleloe.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "anbi2d.mm"
include "wi.mm"
include "potr.mm"
include "com12.mm"
include "breq2.mm"
include "biimpac.mm"
include "a1d.mm"
include "jaodan.mm"
include "sylbid.mm"

theorem poltletr
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cX: class X


  assert |- ( ( R Po X /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A R B /\ B ( R u. _I ) C ) -> A R C ) )

  proof
    cX
    cR
    wpo
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cC
    cX
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cR
    wbr
    #
    cB
    cC
    cR
    cid
    cun
    wbr
    #
    wa
    @6
    cB
    cC
    cR
    wbr
    #
    cB
    cC
    wceq
    #
    wo
    #
    wa
    #
    cA
    cC
    cR
    wbr
    #
    @5
    @7
    @10
    @6
    @4
    @7
    @10
    wb
    #
    @0
    @3
    @1
    @13
    @2
    cB
    cC
    cR
    cX
    poleloe
    3ad2ant3
    adantl
    anbi2d
    @11
    @5
    @12
    @6
    @8
    @5
    @12
    wi
    @9
    @5
    @6
    @8
    wa
    @12
    cX
    cA
    cB
    cC
    cR
    potr
    com12
    @6
    @9
    wa
    @12
    @5
    @9
    @6
    @12
    cB
    cC
    cA
    cR
    breq2
    biimpac
    a1d
    jaodan
    com12
    sylbid
end
