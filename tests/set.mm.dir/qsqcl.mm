include "cq.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "qcn.mm"
include "sqval.mm"
include "syl.mm"
include "qmulcl.mm"
include "anidms.mm"
include "eqeltrd.mm"

theorem qsqcl
  let cA: class A


  assert |- ( A e. QQ -> ( A ^ 2 ) e. QQ )

  proof
    cA
    cq
    wcel
    #
    cA
    c2
    cexp
    co
    #
    cA
    cA
    cmul
    co
    #
    cq
    @0
    cA
    cc
    wcel
    @1
    @2
    wceq
    cA
    qcn
    cA
    sqval
    syl
    @0
    @2
    cq
    wcel
    cA
    cA
    qmulcl
    anidms
    eqeltrd
end
