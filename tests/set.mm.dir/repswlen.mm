include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "creps.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "cfzo.mm"
include "wf.mm"
include "wfn.mm"
include "wceq.mm"
include "repsf.mm"
include "ffn.mm"
include "hashfn.mm"
include "3syl.mm"
include "hashfzo0.mm"
include "adantl.mm"
include "eqtrd.mm"

theorem repswlen
  let cS: class S
  let cN: class N
  let cV: class V


  assert |- ( ( S e. V /\ N e. NN0 ) -> ( # ` ( S repeatS N ) ) = N )

  proof
    cS
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cS
    cN
    creps
    co
    #
    chash
    cfv
    #
    cc0
    cN
    cfzo
    co
    #
    chash
    cfv
    #
    cN
    @2
    @5
    cV
    @3
    wf
    @3
    @5
    wfn
    @4
    @6
    wceq
    cS
    cN
    cV
    repsf
    @5
    cV
    @3
    ffn
    @5
    @3
    hashfn
    3syl
    @1
    @6
    cN
    wceq
    @0
    cN
    hashfzo0
    adantl
    eqtrd
end
