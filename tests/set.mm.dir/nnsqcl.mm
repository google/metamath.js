include "cn.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "cc.mm"
include "wceq.mm"
include "nncn.mm"
include "sqval.mm"
include "syl.mm"
include "nnmulcl.mm"
include "anidms.mm"
include "eqeltrd.mm"

theorem nnsqcl
  let cA: class A


  assert |- ( A e. NN -> ( A ^ 2 ) e. NN )

  proof
    cA
    cn
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
    cn
    @0
    cA
    cc
    wcel
    @1
    @2
    wceq
    cA
    nncn
    cA
    sqval
    syl
    @0
    @2
    cn
    wcel
    cA
    cA
    nnmulcl
    anidms
    eqeltrd
end
