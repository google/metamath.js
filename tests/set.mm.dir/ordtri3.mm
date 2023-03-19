include "word.mm"
include "wa.mm"
include "wceq.mm"
include "wcel.mm"
include "wo.mm"
include "wn.mm"
include "ordirr.mm"
include "adantl.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "pm4.71d.mm"
include "pm5.61.mm"
include "pm4.52.mm"
include "bitr3i.mm"
include "syl6bb.mm"
include "ordtri2.mm"
include "orbi1d.mm"
include "bitr4d.mm"

theorem ordtri3
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A = B <-> -. ( A e. B \/ B e. A ) ) )

  proof
    cA
    word
    #
    cB
    word
    #
    wa
    #
    cA
    cB
    wceq
    #
    @3
    cB
    cA
    wcel
    #
    wo
    #
    wn
    #
    @4
    wo
    #
    wn
    #
    cA
    cB
    wcel
    #
    @4
    wo
    #
    wn
    @2
    @3
    @3
    @4
    wn
    #
    wa
    #
    @8
    @2
    @3
    @11
    @2
    @11
    @3
    cB
    cB
    wcel
    #
    wn
    #
    @1
    @14
    @0
    cB
    ordirr
    adantl
    @3
    @4
    @13
    cA
    cB
    cB
    eleq2
    notbid
    syl5ibrcom
    pm4.71d
    @12
    @5
    @11
    wa
    @8
    @3
    @4
    pm5.61
    @5
    @4
    pm4.52
    bitr3i
    syl6bb
    @2
    @10
    @7
    @2
    @9
    @6
    @4
    cA
    cB
    ordtri2
    orbi1d
    notbid
    bitr4d
end
