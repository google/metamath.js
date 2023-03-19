include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "ccj.mm"
include "cmul.mm"
include "co.mm"
include "csqrt.mm"
include "cre.mm"
include "c2.mm"
include "cexp.mm"
include "cim.mm"
include "caddc.mm"
include "absval.mm"
include "cjmulval.mm"
include "fveq2d.mm"
include "eqtrd.mm"

theorem absval2
  let cA: class A


  assert |- ( A e. CC -> ( abs ` A ) = ( sqrt ` ( ( ( Re ` A ) ^ 2 ) + ( ( Im ` A ) ^ 2 ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    cA
    cA
    ccj
    cfv
    cmul
    co
    #
    csqrt
    cfv
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
    #
    csqrt
    cfv
    cA
    absval
    @0
    @1
    @2
    csqrt
    cA
    cjmulval
    fveq2d
    eqtrd
end
