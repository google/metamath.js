include "c1.mm"
include "cfz.mm"
include "co.mm"
include "wfn.mm"
include "cn0.mm"
include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "hashfn.mm"
include "hashfz1.mm"
include "sylan9eqr.mm"

theorem fseq1hash
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN0 /\ F Fn ( 1 ... N ) ) -> ( # ` F ) = N )

  proof
    cF
    c1
    cN
    cfz
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
    hashfz1
    sylan9eqr
end
