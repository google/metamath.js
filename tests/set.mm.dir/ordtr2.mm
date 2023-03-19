include "word.mm"
include "wa.mm"
include "wss.mm"
include "wcel.mm"
include "wpss.mm"
include "wi.mm"
include "ordelord.mm"
include "ex.mm"
include "ancld.mm"
include "anc2li.mm"
include "ordelpss.mm"
include "sspsstr.mm"
include "expcom.mm"
include "syl6bi.mm"
include "com23.mm"
include "imp32.mm"
include "com12.mm"
include "syl9.mm"
include "impd.mm"
include "adantl.mm"
include "sylibrd.mm"

theorem ordtr2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( Ord A /\ Ord C ) -> ( ( A C_ B /\ B e. C ) -> A e. C ) )

  proof
    cA
    word
    #
    cC
    word
    #
    wa
    cA
    cB
    wss
    #
    cB
    cC
    wcel
    #
    wa
    #
    cA
    cC
    wpss
    #
    cA
    cC
    wcel
    @1
    @4
    @5
    wi
    @0
    @1
    @2
    @3
    @5
    @1
    @3
    @1
    @3
    cB
    word
    #
    wa
    #
    wa
    #
    @2
    @5
    @1
    @3
    @7
    @1
    @3
    @6
    @1
    @3
    @6
    cC
    cB
    ordelord
    ex
    ancld
    anc2li
    @8
    @2
    @5
    @1
    @3
    @6
    @2
    @5
    wi
    #
    @1
    @6
    @3
    @9
    @6
    @1
    @3
    @9
    wi
    @6
    @1
    wa
    @3
    cB
    cC
    wpss
    #
    @9
    cB
    cC
    ordelpss
    @2
    @10
    @5
    cA
    cB
    cC
    sspsstr
    expcom
    syl6bi
    expcom
    com23
    imp32
    com12
    syl9
    impd
    adantl
    cA
    cC
    ordelpss
    sylibrd
end
