include "cat.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "cin.mm"
include "c0h.mm"
include "wceq.mm"
include "cdmd.mm"
include "wbr.mm"
include "chj.mm"
include "co.mm"
include "ccv.mm"
include "wb.mm"
include "cvp.mm"
include "atelch.mm"
include "chjcom.mm"
include "sylan2.mm"
include "breq2d.mm"
include "bitrd.mm"
include "ancoms.mm"
include "wi.mm"
include "cvdmd.mm"
include "3expia.mm"
include "sylan.mm"
include "sylbid.mm"
include "wn.mm"
include "wss.mm"
include "atnssm0.mm"
include "con1bid.mm"
include "ssdmd1.mm"
include "pm2.61d.mm"

theorem atdmd
  let cA: class A
  let cB: class B


  assert |- ( ( A e. HAtoms /\ B e. CH ) -> A MH* B )

  proof
    cA
    cat
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    #
    cB
    cA
    cin
    c0h
    wceq
    #
    cA
    cB
    cdmd
    wbr
    #
    @2
    @3
    cB
    cA
    cB
    chj
    co
    #
    ccv
    wbr
    #
    @4
    @1
    @0
    @3
    @6
    wb
    @1
    @0
    wa
    #
    @3
    cB
    cB
    cA
    chj
    co
    #
    ccv
    wbr
    @6
    cB
    cA
    cvp
    @7
    @8
    @5
    cB
    ccv
    @0
    @1
    cA
    cch
    wcel
    #
    @8
    @5
    wceq
    cA
    atelch
    #
    cB
    cA
    chjcom
    sylan2
    breq2d
    bitrd
    ancoms
    @0
    @9
    @1
    @6
    @4
    wi
    @10
    @9
    @1
    @6
    @4
    cA
    cB
    cvdmd
    3expia
    sylan
    sylbid
    @2
    @3
    wn
    cA
    cB
    wss
    #
    @4
    @2
    @11
    @3
    @1
    @0
    @11
    wn
    @3
    wb
    cB
    cA
    atnssm0
    ancoms
    con1bid
    @0
    @9
    @1
    @11
    @4
    wi
    @10
    @9
    @1
    @11
    @4
    cA
    cB
    ssdmd1
    3expia
    sylan
    sylbid
    pm2.61d
end
