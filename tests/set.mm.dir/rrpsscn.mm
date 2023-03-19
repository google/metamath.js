include "crp.mm"
include "cc.mm"
include "cv.mm"
include "rpcn.mm"
include "ssriv.mm"

theorem rrpsscn
  let vx: setvar x


  assert |- RR+ C_ CC

  proof
    vx
    crp
    cc
    vx
    cv
    rpcn
    ssriv
end
