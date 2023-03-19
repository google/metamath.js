include "cxr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "w3a.mm"
include "elicc1.mm"
include "3anass.mm"
include "syl6bb.mm"
include "baibd.mm"
include "3impa.mm"

theorem elicc4
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. RR* ) -> ( C e. ( A [,] B ) <-> ( A <_ C /\ C <_ B ) ) )

  proof
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cC
    cxr
    wcel
    #
    cC
    cA
    cB
    cicc
    co
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    #
    wa
    #
    wb
    @0
    @1
    wa
    #
    @3
    @2
    @6
    @7
    @3
    @2
    @4
    @5
    w3a
    @2
    @6
    wa
    cA
    cB
    cC
    elicc1
    @2
    @4
    @5
    3anass
    syl6bb
    baibd
    3impa
end
