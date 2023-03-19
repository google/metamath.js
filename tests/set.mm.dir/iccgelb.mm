include "cxr.mm"
include "wcel.mm"
include "cicc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "elicc1.mm"
include "biimpa.mm"
include "simp2d.mm"
include "3impa.mm"

theorem iccgelb
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR* /\ B e. RR* /\ C e. ( A [,] B ) ) -> A <_ C )

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
    cicc
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
    #
    @2
    wa
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
    @4
    @2
    @5
    @3
    @6
    w3a
    cA
    cB
    cC
    elicc1
    biimpa
    simp2d
    3impa
end
