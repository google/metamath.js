include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wn.mm"
include "letri3.mm"
include "wb.mm"
include "lenlt.mm"
include "ancoms.mm"
include "anbi2d.mm"
include "bitrd.mm"

theorem eqlelt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A = B <-> ( A <_ B /\ -. A < B ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wa
    @3
    cA
    cB
    clt
    wbr
    wn
    #
    wa
    cA
    cB
    letri3
    @2
    @4
    @5
    @3
    @1
    @0
    @4
    @5
    wb
    cB
    cA
    lenlt
    ancoms
    anbi2d
    bitrd
end
