include "word.mm"
include "wcel.mm"
include "wa.mm"
include "wpss.mm"
include "ordelord.mm"
include "ex.mm"
include "ancrd.mm"
include "wb.mm"
include "ordelpss.mm"
include "ancoms.mm"
include "biimpd.mm"
include "expimpd.mm"
include "syld.mm"

theorem ordpss
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( Ord B -> ( A e. B -> A C. B ) )

  proof
    cB
    word
    #
    cA
    cB
    wcel
    #
    cA
    word
    #
    @1
    wa
    cA
    cB
    wpss
    #
    @0
    @1
    @2
    @0
    @1
    @2
    cB
    cA
    ordelord
    ex
    ancrd
    @0
    @2
    @1
    @3
    @0
    @2
    wa
    @1
    @3
    @2
    @0
    @1
    @3
    wb
    cA
    cB
    ordelpss
    ancoms
    biimpd
    expimpd
    syld
end
