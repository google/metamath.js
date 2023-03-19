include "word.mm"
include "cuni.mm"
include "wcel.mm"
include "csuc.mm"
include "wi.mm"
include "orduni.mm"
include "ordelord.mm"
include "ex.mm"
include "syl.mm"
include "wa.mm"
include "ordsuc.mm"
include "sylibr.mm"
include "wb.mm"
include "wss.mm"
include "wn.mm"
include "con0.mm"
include "ordsson.mm"
include "ordunisssuc.mm"
include "sylan.mm"
include "ordtri1.mm"
include "sylan2b.mm"
include "3bitr3d.mm"
include "con4bid.mm"
include "pm5.21ndd.mm"

theorem ordsucuniel
  let cA: class A
  let cB: class B


  assert |- ( Ord B -> ( A e. U. B <-> suc A e. B ) )

  proof
    cB
    word
    #
    cA
    word
    #
    cA
    cB
    cuni
    #
    wcel
    #
    cA
    csuc
    #
    cB
    wcel
    #
    @0
    @2
    word
    #
    @3
    @1
    wi
    cB
    orduni
    #
    @6
    @3
    @1
    @2
    cA
    ordelord
    ex
    syl
    @0
    @5
    @1
    @0
    @5
    wa
    @4
    word
    #
    @1
    cB
    @4
    ordelord
    cA
    ordsuc
    #
    sylibr
    ex
    @0
    @1
    @3
    @5
    wb
    @0
    @1
    wa
    #
    @3
    @5
    @10
    @2
    cA
    wss
    #
    cB
    @4
    wss
    #
    @3
    wn
    #
    @5
    wn
    #
    @0
    cB
    con0
    wss
    @1
    @11
    @12
    wb
    cB
    ordsson
    cB
    cA
    ordunisssuc
    sylan
    @0
    @6
    @1
    @11
    @13
    wb
    @7
    @2
    cA
    ordtri1
    sylan
    @1
    @0
    @8
    @12
    @14
    wb
    @9
    cB
    @4
    ordtri1
    sylan2b
    3bitr3d
    con4bid
    ex
    pm5.21ndd
end
