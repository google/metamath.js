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
include "simp3.mm"
include "syl6bi.mm"
include "3impia.mm"

theorem iooltub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. ( A (,) B ) ) -> C < B )

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
    cC
    cB
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
    cA
    cC
    clt
    wbr
    #
    @3
    w3a
    @3
    cA
    cB
    cC
    elioo2
    @4
    @5
    @3
    simp3
    syl6bi
    3impia
end
