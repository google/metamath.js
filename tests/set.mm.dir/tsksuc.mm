include "ctsk.mm"
include "wcel.mm"
include "con0.mm"
include "w3a.mm"
include "cpw.mm"
include "csuc.mm"
include "wss.mm"
include "simp1.mm"
include "tskpw.mm"
include "3adant2.mm"
include "cuni.mm"
include "word.mm"
include "wceq.mm"
include "eloni.mm"
include "3ad2ant2.mm"
include "ordunisuc.mm"
include "eqimss.mm"
include "3syl.mm"
include "sspwuni.mm"
include "sylibr.mm"
include "tskss.mm"
include "syl3anc.mm"

theorem tsksuc
  let cA: class A
  let cT: class T


  assert |- ( ( T e. Tarski /\ A e. On /\ A e. T ) -> suc A e. T )

  proof
    cT
    ctsk
    wcel
    #
    cA
    con0
    wcel
    #
    cA
    cT
    wcel
    #
    w3a
    #
    @0
    cA
    cpw
    #
    cT
    wcel
    #
    cA
    csuc
    #
    @4
    wss
    #
    @6
    cT
    wcel
    @0
    @1
    @2
    simp1
    @0
    @2
    @5
    @1
    cA
    cT
    tskpw
    3adant2
    @3
    @6
    cuni
    #
    cA
    wss
    #
    @7
    @3
    cA
    word
    #
    @8
    cA
    wceq
    @9
    @1
    @0
    @10
    @2
    cA
    eloni
    3ad2ant2
    cA
    ordunisuc
    @8
    cA
    eqimss
    3syl
    @6
    cA
    sspwuni
    sylibr
    @4
    @6
    cT
    tskss
    syl3anc
end
