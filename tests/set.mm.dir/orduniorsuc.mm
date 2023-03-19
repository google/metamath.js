include "word.mm"
include "cuni.mm"
include "wceq.mm"
include "csuc.mm"
include "wne.mm"
include "wss.mm"
include "wa.mm"
include "wn.mm"
include "wcel.mm"
include "orduniss.mm"
include "wb.mm"
include "orduni.mm"
include "ordelssne.mm"
include "mpancom.mm"
include "biimprd.mm"
include "mpand.mm"
include "ordsucss.mm"
include "syld.mm"
include "ordsucuni.mm"
include "jctild.mm"
include "df-ne.mm"
include "necom.mm"
include "bitr3i.mm"
include "eqss.mm"
include "3imtr4g.mm"
include "orrd.mm"

theorem orduniorsuc
  let cA: class A


  assert |- ( Ord A -> ( A = U. A \/ A = suc U. A ) )

  proof
    cA
    word
    #
    cA
    cA
    cuni
    #
    wceq
    #
    cA
    @1
    csuc
    #
    wceq
    #
    @0
    @1
    cA
    wne
    #
    cA
    @3
    wss
    #
    @3
    cA
    wss
    #
    wa
    @2
    wn
    #
    @4
    @0
    @5
    @7
    @6
    @0
    @5
    @1
    cA
    wcel
    #
    @7
    @0
    @1
    cA
    wss
    #
    @5
    @9
    cA
    orduniss
    @0
    @9
    @10
    @5
    wa
    #
    @1
    word
    @0
    @9
    @11
    wb
    cA
    orduni
    @1
    cA
    ordelssne
    mpancom
    biimprd
    mpand
    @1
    cA
    ordsucss
    syld
    cA
    ordsucuni
    jctild
    @8
    cA
    @1
    wne
    @5
    cA
    @1
    df-ne
    cA
    @1
    necom
    bitr3i
    cA
    @3
    eqss
    3imtr4g
    orrd
end
