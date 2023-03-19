include "crrvec.mm"
include "ccmn.mm"
include "bj-rrvecsscmn.mm"
include "sseli.mm"

theorem bj-rrvecsscmnel
  let cA: class A


  assert |- ( A e. RRVec -> A e. CMnd )

  proof
    crrvec
    ccmn
    cA
    bj-rrvecsscmn
    sseli
end
