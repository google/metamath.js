include "cxr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "simp2.mm"
include "simp3.mm"
include "xrleid.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "elicc1.mm"
include "3adant3.mm"
include "mpbir3and.mm"

theorem ubicc2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR* /\ B e. RR* /\ A <_ B ) -> B e. ( A [,] B ) )

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
    cB
    cA
    cB
    cicc
    co
    wcel
    #
    @1
    @2
    cB
    cB
    cle
    wbr
    #
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    @1
    @0
    @4
    @2
    cB
    xrleid
    3ad2ant2
    @0
    @1
    @3
    @1
    @2
    @4
    w3a
    wb
    @2
    cA
    cB
    cB
    elicc1
    3adant3
    mpbir3and
end
