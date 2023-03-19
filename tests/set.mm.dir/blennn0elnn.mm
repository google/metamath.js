include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cblen.mm"
include "cfv.mm"
include "elnn0.mm"
include "blennnelnn.mm"
include "fveq2.mm"
include "c1.mm"
include "blen0.mm"
include "1nn.mm"
include "eqeltri.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem blennn0elnn
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( #b ` N ) e. NN )

  proof
    cN
    cn0
    wcel
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cN
    cblen
    cfv
    #
    cn
    wcel
    #
    cN
    elnn0
    @0
    @3
    @1
    cN
    blennnelnn
    @1
    @2
    cc0
    cblen
    cfv
    #
    cn
    cN
    cc0
    cblen
    fveq2
    @4
    c1
    cn
    blen0
    1nn
    eqeltri
    syl6eqel
    jaoi
    sylbi
end
