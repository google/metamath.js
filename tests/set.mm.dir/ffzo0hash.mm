include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wfn.mm"
include "cn0.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "hashfn.mm"
include "hashfzo0.mm"
include "sylan9eqr.mm"

theorem ffzo0hash
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN0 /\ F Fn ( 0 ..^ N ) ) -> ( # ` F ) = N )

  proof
    cF
    cc0
    cN
    cfzo
    co
    #
    wfn
    cN
    cn0
    wcel
    cF
    chash
    cfv
    @0
    chash
    cfv
    cN
    @0
    cF
    hashfn
    cN
    hashfzo0
    sylan9eqr
end
