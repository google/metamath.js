include "ctsk.mm"
include "wcel.mm"
include "wtr.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "cuni.mm"
include "cint.mm"
include "wss.mm"
include "simp1l.mm"
include "tskuni.mm"
include "3expa.mm"
include "3adant3.mm"
include "intssuni.mm"
include "3ad2ant3.mm"
include "tskss.mm"
include "syl3anc.mm"

theorem tskint
  let cA: class A
  let cT: class T


  assert |- ( ( ( T e. Tarski /\ Tr T ) /\ A e. T /\ A =/= (/) ) -> |^| A e. T )

  proof
    cT
    ctsk
    wcel
    #
    cT
    wtr
    #
    wa
    #
    cA
    cT
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    @0
    cA
    cuni
    #
    cT
    wcel
    #
    cA
    cint
    #
    @5
    wss
    #
    @7
    cT
    wcel
    @0
    @1
    @3
    @4
    simp1l
    @2
    @3
    @6
    @4
    @0
    @1
    @3
    @6
    cA
    cT
    tskuni
    3expa
    3adant3
    @4
    @2
    @8
    @3
    cA
    intssuni
    3ad2ant3
    @5
    @7
    cT
    tskss
    syl3anc
end
