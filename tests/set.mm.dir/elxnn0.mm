include "cxnn0.mm"
include "wcel.mm"
include "cn0.mm"
include "cpnf.mm"
include "csn.mm"
include "cun.mm"
include "wo.mm"
include "wceq.mm"
include "df-xnn0.mm"
include "eleq2i.mm"
include "elun.mm"
include "pnfex.mm"
include "elsn2.mm"
include "orbi2i.mm"
include "3bitri.mm"

theorem elxnn0
  let cA: class A


  assert |- ( A e. NN0* <-> ( A e. NN0 \/ A = +oo ) )

  proof
    cA
    cxnn0
    wcel
    cA
    cn0
    cpnf
    csn
    #
    cun
    #
    wcel
    cA
    cn0
    wcel
    #
    cA
    @0
    wcel
    #
    wo
    @2
    cA
    cpnf
    wceq
    #
    wo
    cxnn0
    @1
    cA
    df-xnn0
    eleq2i
    cA
    cn0
    @0
    elun
    @3
    @4
    @2
    cA
    cpnf
    pnfex
    elsn2
    orbi2i
    3bitri
end
