include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "ctg.mm"
include "cfv.mm"
include "ctop.mm"
include "ontgsucval.mm"
include "ctb.mm"
include "suceloni.mm"
include "ontopbas.mm"
include "tgcl.mm"
include "3syl.mm"
include "eqeltrrd.mm"

theorem onsuctop
  let cA: class A


  assert |- ( A e. On -> suc A e. Top )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    #
    ctg
    cfv
    #
    @1
    ctop
    cA
    ontgsucval
    @0
    @1
    con0
    wcel
    @1
    ctb
    wcel
    @2
    ctop
    wcel
    cA
    suceloni
    @1
    ontopbas
    @1
    tgcl
    3syl
    eqeltrrd
end
