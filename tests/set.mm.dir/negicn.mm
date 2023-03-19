include "ci.mm"
include "cc.mm"
include "wcel.mm"
include "cneg.mm"
include "ax-icn.mm"
include "negcl.mm"
include "ax-mp.mm"

theorem negicn



  assert |- -u _i e. CC

  proof
    ci
    cc
    wcel
    ci
    cneg
    cc
    wcel
    ax-icn
    ci
    negcl
    ax-mp
end
