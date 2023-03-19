include "cxr.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmnf.mm"
include "clt.mm"
include "ge0gtmnf.mm"
include "ad2ant2r.mm"
include "simprr.mm"
include "jca.mm"
include "xrre.mm"
include "syldan.mm"

theorem xrrege0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR* /\ B e. RR ) /\ ( 0 <_ A /\ A <_ B ) ) -> A e. RR )

  proof
    cA
    cxr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    wa
    #
    cmnf
    cA
    clt
    wbr
    #
    @4
    wa
    cA
    cr
    wcel
    @2
    @5
    wa
    @6
    @4
    @0
    @3
    @6
    @1
    @4
    cA
    ge0gtmnf
    ad2ant2r
    @2
    @3
    @4
    simprr
    jca
    cA
    cB
    xrre
    syldan
end
