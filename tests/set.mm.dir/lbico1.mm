include "cxr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "simp1.mm"
include "xrleid.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "wb.mm"
include "elico1.mm"
include "3adant3.mm"
include "mpbir3and.mm"

theorem lbico1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* /\ A < B ) -> A e. ( A [,) B ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    cA
    cA
    cB
    cico
    co
    wcel
    #
    @0
    cA
    cA
    cle
    wbr
    #
    @2
    @0
    @1
    @2
    simp1
    @0
    @1
    @4
    @2
    cA
    xrleid
    3ad2ant1
    @0
    @1
    @2
    simp3
    @0
    @1
    @3
    @0
    @4
    @2
    w3a
    wb
    @2
    cA
    cB
    cA
    elico1
    3adant3
    mpbir3and
end
