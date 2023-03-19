include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "simp1.mm"
include "xrleid.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "wb.mm"
include "elicc1.mm"
include "3adant3.mm"
include "mpbir3and.mm"

theorem lbicc2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) -> A e. ( A [,] B ) )

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
    cle
    wbr
    #
    w3a
    cA
    cA
    cB
    cicc
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
    elicc1
    3adant3
    mpbir3and
end
