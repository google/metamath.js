include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "cc0.mm"
include "cmin.mm"
include "co.mm"
include "df-neg.mm"
include "0cn.mm"
include "subcl.mm"
include "mpan.mm"
include "syl5eqel.mm"

theorem negcl
  let cA: class A


  assert |- ( A e. CC -> -u A e. CC )

  proof
    cA
    cc
    wcel
    #
    cA
    cneg
    cc0
    cA
    cmin
    co
    #
    cc
    cA
    df-neg
    cc0
    cc
    wcel
    @0
    @1
    cc
    wcel
    0cn
    cc0
    cA
    subcl
    mpan
    syl5eqel
end
