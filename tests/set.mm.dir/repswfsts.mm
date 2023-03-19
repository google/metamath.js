include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cn0.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "creps.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "nnnn0.mm"
include "adantl.mm"
include "lbfzo0.mm"
include "biimpri.mm"
include "repswsymb.mm"
include "syl3anc.mm"

theorem repswfsts
  let cS: class S
  let cN: class N
  let cV: class V


  assert |- ( ( S e. V /\ N e. NN ) -> ( ( S repeatS N ) ` 0 ) = S )

  proof
    cS
    cV
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    @0
    cN
    cn0
    wcel
    #
    cc0
    cc0
    cN
    cfzo
    co
    wcel
    #
    cc0
    cS
    cN
    creps
    co
    cfv
    cS
    wceq
    @0
    @1
    simpl
    @1
    @2
    @0
    cN
    nnnn0
    adantl
    @1
    @3
    @0
    @3
    @1
    cN
    lbfzo0
    biimpri
    adantl
    cS
    cc0
    cN
    cV
    repswsymb
    syl3anc
end
