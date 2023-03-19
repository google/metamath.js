include "cc.mm"
include "wcel.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "c1.mm"
include "efcl.mm"
include "negcl.mm"
include "syl.mm"
include "efne0.mm"
include "efcan.mm"
include "mvllmuld.mm"

theorem efneg
  let cA: class A


  assert |- ( A e. CC -> ( exp ` -u A ) = ( 1 / ( exp ` A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ce
    cfv
    cA
    cneg
    #
    ce
    cfv
    #
    c1
    cA
    efcl
    @0
    @1
    cc
    wcel
    @2
    cc
    wcel
    cA
    negcl
    @1
    efcl
    syl
    cA
    efne0
    cA
    efcan
    mvllmuld
end
