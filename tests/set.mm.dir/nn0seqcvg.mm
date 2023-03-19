include "c1.mm"
include "wceq.mm"
include "cfv.mm"
include "cc0.mm"
include "eqid.mm"
include "cn0.mm"
include "wf.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "adantl.mm"
include "nn0seqcvgd.mm"
include "ax-mp.mm"

theorem nn0seqcvg
  let vk: setvar k
  let cF: class F
  let cN: class N
  assume nn0seqcvg.1: |- F : NN0 --> NN0
  assume nn0seqcvg.2: |- N = ( F ` 0 )
  assume nn0seqcvg.3: |- ( k e. NN0 -> ( ( F ` ( k + 1 ) ) =/= 0 -> ( F ` ( k + 1 ) ) < ( F ` k ) ) )

  disjoint F k
  disjoint N k
  assert |- ( F ` N ) = 0

  proof
    c1
    c1
    wceq
    #
    cN
    cF
    cfv
    cc0
    wceq
    c1
    eqid
    @0
    vk
    cF
    cN
    cn0
    cn0
    cF
    wf
    @0
    nn0seqcvg.1
    a1i
    cN
    cc0
    cF
    cfv
    wceq
    @0
    nn0seqcvg.2
    a1i
    vk
    cv
    #
    cn0
    wcel
    @1
    c1
    caddc
    co
    cF
    cfv
    #
    cc0
    wne
    @2
    @1
    cF
    cfv
    clt
    wbr
    wi
    @0
    nn0seqcvg.3
    adantl
    nn0seqcvgd
    ax-mp
end
