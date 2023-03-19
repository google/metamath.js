include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "3simpb.mm"
include "lelttr.mm"
include "ltle.mm"
include "sylsyld.mm"

theorem leltletr
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A <_ B /\ B < C ) -> A <_ C ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    @0
    @2
    wa
    cA
    cB
    cle
    wbr
    cB
    cC
    clt
    wbr
    wa
    cA
    cC
    clt
    wbr
    cA
    cC
    cle
    wbr
    @0
    @1
    @2
    3simpb
    cA
    cB
    cC
    lelttr
    cA
    cC
    ltle
    sylsyld
end
