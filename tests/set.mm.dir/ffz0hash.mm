include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wf.mm"
include "cn0.mm"
include "wcel.mm"
include "wfn.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "ffn.mm"
include "fnfz0hash.mm"
include "sylan2.mm"

theorem ffz0hash
  let cB: class B
  let cF: class F
  let cN: class N


  assert |- ( ( N e. NN0 /\ F : ( 0 ... N ) --> B ) -> ( # ` F ) = ( N + 1 ) )

  proof
    cc0
    cN
    cfz
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
    c1
    caddc
    co
    wceq
    @0
    cB
    cF
    ffn
    cF
    cN
    fnfz0hash
    sylan2
end
