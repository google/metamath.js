include "ctsk.mm"
include "wcel.mm"
include "w3a.mm"
include "cpr.mm"
include "wss.mm"
include "csdm.mm"
include "wbr.mm"
include "simp1.mm"
include "prssi.mm"
include "3adant1.mm"
include "wa.mm"
include "com.mm"
include "cdom.mm"
include "cfn.mm"
include "prfi.mm"
include "isfinite.mm"
include "mpbi.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "tskinf.mm"
include "sylan2.mm"
include "sdomdomtr.mm"
include "sylancr.mm"
include "3adant3.mm"
include "tskssel.mm"
include "syl3anc.mm"

theorem tskpr
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( T e. Tarski /\ A e. T /\ B e. T ) -> { A , B } e. T )

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
    @0
    cA
    cB
    cpr
    #
    cT
    wss
    #
    @3
    cT
    csdm
    wbr
    #
    @3
    cT
    wcel
    @0
    @1
    @2
    simp1
    @1
    @2
    @4
    @0
    cA
    cB
    cT
    prssi
    3adant1
    @0
    @1
    @5
    @2
    @0
    @1
    wa
    @3
    com
    csdm
    wbr
    #
    com
    cT
    cdom
    wbr
    #
    @5
    @3
    cfn
    wcel
    @6
    cA
    cB
    prfi
    @3
    isfinite
    mpbi
    @1
    @0
    cT
    c0
    wne
    @7
    cT
    cA
    ne0i
    cT
    tskinf
    sylan2
    @3
    com
    cT
    sdomdomtr
    sylancr
    3adant3
    @3
    cT
    tskssel
    syl3anc
end
