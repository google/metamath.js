include "cxr.mm"
include "wcel.mm"
include "cioo.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "w3a.mm"
include "elioo2.mm"
include "simp2.mm"
include "syl6bi.mm"
include "3impia.mm"

theorem ioogtlb
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. ( A (,) B ) ) -> A < C )

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
    cioo
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
    cr
    wcel
    #
    @3
    cC
    cB
    clt
    wbr
    #
    w3a
    @3
    cA
    cB
    cC
    elioo2
    @4
    @3
    @5
    simp2
    syl6bi
    3impia
end
