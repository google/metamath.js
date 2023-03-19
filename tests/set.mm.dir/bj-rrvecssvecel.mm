include "crrvec.mm"
include "clvec.mm"
include "bj-rrvecssvec.mm"
include "sseli.mm"

theorem bj-rrvecssvecel
  let cA: class A


  assert |- ( A e. RRVec -> A e. LVec )

  proof
    crrvec
    clvec
    cA
    bj-rrvecssvec
    sseli
end
