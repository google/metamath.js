include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "3simpb.mm"
include "ltletr.mm"
include "ltle.mm"
include "sylsyld.mm"

theorem ltleletr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( ( A < B /\ B <_ C ) -> A <_ C ) )

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
    clt
    wbr
    cB
    cC
    cle
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
    ltletr
    cA
    cC
    ltle
    sylsyld
end
