include "ctsk.mm"
include "wcel.mm"
include "wtr.mm"
include "wa.mm"
include "w3a.mm"
include "cpr.mm"
include "cuni.mm"
include "cun.mm"
include "wceq.mm"
include "uniprg.mm"
include "3adant1.mm"
include "simp1l.mm"
include "simp1r.mm"
include "tskpr.mm"
include "3adant1r.mm"
include "tskuni.mm"
include "syl3anc.mm"
include "eqeltrrd.mm"

theorem tskun
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( ( T e. Tarski /\ Tr T ) /\ A e. T /\ B e. T ) -> ( A u. B ) e. T )

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
    cB
    cT
    wcel
    #
    w3a
    #
    cA
    cB
    cpr
    #
    cuni
    #
    cA
    cB
    cun
    #
    cT
    @3
    @4
    @7
    @8
    wceq
    @2
    cA
    cB
    cT
    cT
    uniprg
    3adant1
    @5
    @0
    @1
    @6
    cT
    wcel
    #
    @7
    cT
    wcel
    @0
    @1
    @3
    @4
    simp1l
    @0
    @1
    @3
    @4
    simp1r
    @0
    @3
    @4
    @9
    @1
    cA
    cB
    cT
    tskpr
    3adant1r
    @6
    cT
    tskuni
    syl3anc
    eqeltrrd
end
