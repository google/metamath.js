include "word.mm"
include "wa.mm"
include "wss.mm"
include "wcel.mm"
include "wceq.mm"
include "wo.mm"
include "wn.mm"
include "ordsseleq.mm"
include "wi.mm"
include "ordn2lp.mm"
include "imnan.mm"
include "sylibr.mm"
include "ordirr.mm"
include "eleq2.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "jaao.mm"
include "w3o.mm"
include "ordtri3or.mm"
include "df-3or.mm"
include "sylib.mm"
include "orcomd.mm"
include "ord.mm"
include "impbid.mm"
include "bitrd.mm"

theorem ordtri1
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> ( A C_ B <-> -. B e. A ) )

  proof
    cA
    word
    #
    cB
    word
    #
    wa
    #
    cA
    cB
    wss
    cA
    cB
    wcel
    #
    cA
    cB
    wceq
    #
    wo
    #
    cB
    cA
    wcel
    #
    wn
    #
    cA
    cB
    ordsseleq
    @2
    @5
    @7
    @0
    @3
    @7
    @1
    @4
    @0
    @3
    @6
    wa
    wn
    @3
    @7
    wi
    cA
    cB
    ordn2lp
    @3
    @6
    imnan
    sylibr
    @1
    @7
    @4
    cB
    cB
    wcel
    #
    wn
    cB
    ordirr
    @4
    @6
    @8
    cA
    cB
    cB
    eleq2
    notbid
    syl5ibrcom
    jaao
    @2
    @6
    @5
    @2
    @5
    @6
    @2
    @3
    @4
    @6
    w3o
    @5
    @6
    wo
    cA
    cB
    ordtri3or
    @3
    @4
    @6
    df-3or
    sylib
    orcomd
    ord
    impbid
    bitrd
end
