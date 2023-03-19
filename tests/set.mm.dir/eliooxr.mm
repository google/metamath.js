include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cxr.mm"
include "wa.mm"
include "ne0i.mm"
include "ndmioo.mm"
include "necon1ai.mm"
include "syl.mm"

theorem eliooxr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B (,) C ) -> ( B e. RR* /\ C e. RR* ) )

  proof
    cA
    cB
    cC
    cioo
    co
    #
    wcel
    @0
    c0
    wne
    cB
    cxr
    wcel
    cC
    cxr
    wcel
    wa
    #
    @0
    cA
    ne0i
    @1
    @0
    c0
    cB
    cC
    ndmioo
    necon1ai
    syl
end
