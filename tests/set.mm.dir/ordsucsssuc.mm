include "word.mm"
include "wa.mm"
include "wcel.mm"
include "wn.mm"
include "csuc.mm"
include "wss.mm"
include "wb.mm"
include "ordsucelsuc.mm"
include "notbid.mm"
include "adantr.mm"
include "ordtri1.mm"
include "ordsuc.mm"
include "syl2anb.mm"
include "3bitr4d.mm"

theorem ordsucsssuc
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> suc A C_ suc B ) )

  proof
    cA
    word
    #
    cB
    word
    #
    wa
    cB
    cA
    wcel
    #
    wn
    #
    cB
    csuc
    #
    cA
    csuc
    #
    wcel
    #
    wn
    #
    cA
    cB
    wss
    @5
    @4
    wss
    #
    @0
    @3
    @7
    wb
    @1
    @0
    @2
    @6
    cB
    cA
    ordsucelsuc
    notbid
    adantr
    cA
    cB
    ordtri1
    @0
    @5
    word
    @4
    word
    @8
    @7
    wb
    @1
    cA
    ordsuc
    cB
    ordsuc
    @5
    @4
    ordtri1
    syl2anb
    3bitr4d
end
