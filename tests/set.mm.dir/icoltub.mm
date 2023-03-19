include "cxr.mm"
include "wcel.mm"
include "cico.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "w3a.mm"
include "elico1.mm"
include "simp3.mm"
include "syl6bi.mm"
include "3impia.mm"

theorem icoltub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. ( A [,) B ) ) -> C < B )

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
    cico
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
    cxr
    wcel
    #
    cA
    cC
    cle
    wbr
    #
    @3
    w3a
    @3
    cA
    cB
    cC
    elico1
    @4
    @5
    @3
    simp3
    syl6bi
    3impia
end
