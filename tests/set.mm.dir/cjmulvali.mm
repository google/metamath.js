include "cc.mm"
include "wcel.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "cre.mm"
include "c2.mm"
include "cexp.mm"
include "cim.mm"
include "caddc.mm"
include "wceq.mm"
include "cjmulval.mm"
include "ax-mp.mm"

theorem cjmulvali
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- ( A x. ( * ` A ) ) = ( ( ( Re ` A ) ^ 2 ) + ( ( Im ` A ) ^ 2 ) )

  proof
    cA
    cc
    wcel
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
    wceq
    recl.1
    cA
    cjmulval
    ax-mp
end
