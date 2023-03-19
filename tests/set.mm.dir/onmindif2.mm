include "con0.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "cv.mm"
include "wral.mm"
include "eldifsn.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "onnmin.mm"
include "adantlr.mm"
include "wb.mm"
include "oninton.mm"
include "adantr.mm"
include "ssel2.mm"
include "ontri1.mm"
include "onsseleq.mm"
include "bitr3d.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ord.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "necon1ad.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "cvv.mm"
include "intex.mm"
include "elintg.mm"
include "sylbi.mm"
include "adantl.mm"
include "mpbird.mm"

theorem onmindif2
  let cA: class A
  let vx: setvar x


  assert |- ( ( A C_ On /\ A =/= (/) ) -> |^| A e. |^| ( A \ { |^| A } ) )

  proof
    cA
    con0
    wss
    #
    cA
    c0
    wne
    #
    wa
    #
    cA
    cint
    #
    cA
    @3
    csn
    cdif
    #
    cint
    wcel
    #
    @3
    vx
    cv
    #
    wcel
    #
    vx
    @4
    wral
    #
    @2
    @7
    vx
    @4
    @6
    @4
    wcel
    @6
    cA
    wcel
    #
    @6
    @3
    wne
    #
    wa
    @2
    @7
    @6
    cA
    @3
    eldifsn
    @2
    @9
    @10
    @7
    @2
    @9
    wa
    #
    @7
    @6
    @3
    @11
    @7
    wn
    @3
    @6
    wceq
    #
    @6
    @3
    wceq
    @11
    @7
    @12
    @11
    @6
    @3
    wcel
    wn
    #
    @7
    @12
    wo
    #
    @0
    @9
    @13
    @1
    cA
    @6
    onnmin
    adantlr
    @11
    @3
    con0
    wcel
    #
    @6
    con0
    wcel
    #
    @13
    @14
    wb
    @2
    @15
    @9
    cA
    oninton
    adantr
    @0
    @9
    @16
    @1
    cA
    con0
    @6
    ssel2
    adantlr
    @15
    @16
    wa
    @3
    @6
    wss
    @13
    @14
    @3
    @6
    ontri1
    @3
    @6
    onsseleq
    bitr3d
    syl2anc
    mpbid
    ord
    @3
    @6
    eqcom
    syl6ib
    necon1ad
    expimpd
    syl5bi
    ralrimiv
    @1
    @5
    @8
    wb
    #
    @0
    @1
    @3
    cvv
    wcel
    @17
    cA
    intex
    vx
    @3
    @4
    cvv
    elintg
    sylbi
    adantl
    mpbird
end
