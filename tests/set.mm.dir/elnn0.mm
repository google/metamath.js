include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "csn.mm"
include "cun.mm"
include "wo.mm"
include "wceq.mm"
include "df-n0.mm"
include "eleq2i.mm"
include "elun.mm"
include "c0ex.mm"
include "elsn2.mm"
include "orbi2i.mm"
include "3bitri.mm"

theorem elnn0
  let cA: class A


  assert |- ( A e. NN0 <-> ( A e. NN \/ A = 0 ) )

  proof
    cA
    cn0
    wcel
    cA
    cn
    cc0
    csn
    #
    cun
    #
    wcel
    cA
    cn
    wcel
    #
    cA
    @0
    wcel
    #
    wo
    @2
    cA
    cc0
    wceq
    #
    wo
    cn0
    @1
    cA
    df-n0
    eleq2i
    cA
    cn
    @0
    elun
    @3
    @4
    @2
    cA
    cc0
    c0ex
    elsn2
    orbi2i
    3bitri
end
