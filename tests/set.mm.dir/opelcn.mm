include "cop.mm"
include "cc.mm"
include "wcel.mm"
include "cnr.mm"
include "cxp.mm"
include "wa.mm"
include "df-c.mm"
include "eleq2i.mm"
include "opelxp.mm"
include "bitri.mm"

theorem opelcn
  let cA: class A
  let cB: class B


  assert |- ( <. A , B >. e. CC <-> ( A e. R. /\ B e. R. ) )

  proof
    cA
    cB
    cop
    #
    cc
    wcel
    @0
    cnr
    cnr
    cxp
    #
    wcel
    cA
    cnr
    wcel
    cB
    cnr
    wcel
    wa
    cc
    @1
    @0
    df-c
    eleq2i
    cA
    cB
    cnr
    cnr
    opelxp
    bitri
end
