include "ctsk.mm"
include "wcel.mm"
include "w3a.mm"
include "cop.mm"
include "csn.mm"
include "cpr.mm"
include "wceq.mm"
include "dfopg.mm"
include "3adant1.mm"
include "simp1.mm"
include "tsksn.mm"
include "3adant3.mm"
include "tskpr.mm"
include "syl3anc.mm"
include "eqeltrd.mm"

theorem tskop
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( T e. Tarski /\ A e. T /\ B e. T ) -> <. A , B >. e. T )

  proof
    cT
    ctsk
    wcel
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
    cop
    #
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    cT
    @1
    @2
    @4
    @7
    wceq
    @0
    cA
    cB
    cT
    cT
    dfopg
    3adant1
    @3
    @0
    @5
    cT
    wcel
    #
    @6
    cT
    wcel
    @7
    cT
    wcel
    @0
    @1
    @2
    simp1
    @0
    @1
    @8
    @2
    cA
    cT
    tsksn
    3adant3
    cA
    cB
    cT
    tskpr
    @5
    @6
    cT
    tskpr
    syl3anc
    eqeltrd
end
