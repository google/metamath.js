include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cmul.mm"
include "co.mm"
include "id.mm"
include "0red.mm"
include "lttri2d.mm"
include "biimpa.mm"
include "wa.mm"
include "mullt0.mm"
include "anidms.mm"
include "mulgt0.mm"
include "jaodan.mm"
include "syldan.mm"

theorem msqgt0
  let cA: class A


  assert |- ( ( A e. RR /\ A =/= 0 ) -> 0 < ( A x. A ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    wne
    #
    cA
    cc0
    clt
    wbr
    #
    cc0
    cA
    clt
    wbr
    #
    wo
    #
    cc0
    cA
    cA
    cmul
    co
    clt
    wbr
    #
    @0
    @1
    @4
    @0
    cA
    cc0
    @0
    id
    @0
    0red
    lttri2d
    biimpa
    @0
    @2
    @5
    @3
    @0
    @2
    wa
    @5
    cA
    cA
    mullt0
    anidms
    @0
    @3
    wa
    @5
    cA
    cA
    mulgt0
    anidms
    jaodan
    syldan
end
