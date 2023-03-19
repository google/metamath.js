include "cxr.mm"
include "wcel.mm"
include "cioc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "w3a.mm"
include "elioc1.mm"
include "simp2.mm"
include "syl6bi.mm"
include "3impia.mm"

theorem iocgtlb
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. ( A (,] B ) ) -> A < C )

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
    cA
    cB
    cioc
    co
    wcel
    #
    cA
    cC
    clt
    wbr
    #
    @0
    @1
    wa
    @2
    cC
    cxr
    wcel
    #
    @3
    cC
    cB
    cle
    wbr
    #
    w3a
    @3
    cA
    cB
    cC
    elioc1
    @4
    @3
    @5
    simp2
    syl6bi
    3impia
end
