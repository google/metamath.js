include "cxr.mm"
include "wcel.mm"
include "cico.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "w3a.mm"
include "elico1.mm"
include "simp2.mm"
include "syl6bi.mm"
include "3impia.mm"

theorem icogelb
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. ( A [,) B ) ) -> A <_ C )

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
    cA
    cC
    cle
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
    clt
    wbr
    #
    w3a
    @3
    cA
    cB
    cC
    elico1
    @4
    @3
    @5
    simp2
    syl6bi
    3impia
end
