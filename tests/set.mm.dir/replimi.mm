include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "ci.mm"
include "cim.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "replim.mm"
include "ax-mp.mm"

theorem replimi
  let cA: class A
  assume recl.1: |- A e. CC


  assert |- A = ( ( Re ` A ) + ( _i x. ( Im ` A ) ) )

  proof
    cA
    cc
    wcel
    cA
    cA
    cre
    cfv
    ci
    cA
    cim
    cfv
    cmul
    co
    caddc
    co
    wceq
    recl.1
    cA
    replim
    ax-mp
end
