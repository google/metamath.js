include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "ccj.mm"
include "cmul.mm"
include "cre.mm"
include "cim.mm"
include "caddc.mm"
include "absvalsq.mm"
include "cjmulval.mm"
include "eqtrd.mm"

theorem absvalsq2
  let cA: class A


  assert |- ( A e. CC -> ( ( abs ` A ) ^ 2 ) = ( ( ( Re ` A ) ^ 2 ) + ( ( Im ` A ) ^ 2 ) ) )

  proof
    cA
    cc
    wcel
    cA
    cabs
    cfv
    c2
    cexp
    co
    cA
    cA
    ccj
    cfv
    cmul
    co
    cA
    cre
    cfv
    c2
    cexp
    co
    cA
    cim
    cfv
    c2
    cexp
    co
    caddc
    co
    cA
    absvalsq
    cA
    cjmulval
    eqtrd
end
