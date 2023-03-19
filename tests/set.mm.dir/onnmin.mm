include "con0.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cint.mm"
include "wn.mm"
include "intss1.mm"
include "adantl.mm"
include "wb.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "oninton.mm"
include "sylan2.mm"
include "ssel2.mm"
include "ontri1.mm"
include "syl2anc.mm"
include "mpbid.mm"

theorem onnmin
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ On /\ B e. A ) -> -. B e. |^| A )

  proof
    cA
    con0
    wss
    #
    cB
    cA
    wcel
    #
    wa
    #
    cA
    cint
    #
    cB
    wss
    #
    cB
    @3
    wcel
    wn
    #
    @1
    @4
    @0
    cB
    cA
    intss1
    adantl
    @2
    @3
    con0
    wcel
    #
    cB
    con0
    wcel
    @4
    @5
    wb
    @1
    @0
    cA
    c0
    wne
    @6
    cA
    cB
    ne0i
    cA
    oninton
    sylan2
    cA
    con0
    cB
    ssel2
    @3
    cB
    ontri1
    syl2anc
    mpbid
end
