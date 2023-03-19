include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cn0.mm"
include "wcel.mm"
include "wfn.mm"
include "chash.mm"
include "cfv.mm"
include "wceq.mm"
include "ffn.mm"
include "ffzo0hash.mm"
include "sylan2.mm"

theorem fnfzo0hash
  let cB: class B
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN0 /\ F : ( 0 ..^ N ) --> B ) -> ( # ` F ) = N )

  proof
    cc0
    cN
    cfzo
    co
    #
    cB
    cF
    wf
    cN
    cn0
    wcel
    cF
    @0
    wfn
    cF
    chash
    cfv
    cN
    wceq
    @0
    cB
    cF
    ffn
    cF
    cN
    ffzo0hash
    sylan2
end
