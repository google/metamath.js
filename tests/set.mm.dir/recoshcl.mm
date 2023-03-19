include "cr.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "cfv.mm"
include "rpcoshcl.mm"
include "rpred.mm"

theorem recoshcl
  let cA: class A


  assert |- ( A e. RR -> ( cos ` ( _i x. A ) ) e. RR )

  proof
    cA
    cr
    wcel
    ci
    cA
    cmul
    co
    ccos
    cfv
    cA
    rpcoshcl
    rpred
end
