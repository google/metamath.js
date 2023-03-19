include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cmul.mm"
include "sqval.mm"
include "mulcl.mm"
include "anidms.mm"
include "eqeltrd.mm"

theorem sqcl
  let cA: class A


  assert |- ( A e. CC -> ( A ^ 2 ) e. CC )

  proof
    cA
    cc
    wcel
    #
    cA
    c2
    cexp
    co
    cA
    cA
    cmul
    co
    #
    cc
    cA
    sqval
    @0
    @1
    cc
    wcel
    cA
    cA
    mulcl
    anidms
    eqeltrd
end
