include "cn0.mm"
include "wcel.mm"
include "cfzo.mm"
include "co.mm"
include "cc0.mm"
include "cfz.mm"
include "fzossfz.mm"
include "wss.mm"
include "cuz.mm"
include "cfv.mm"
include "fzss1.mm"
include "nn0uz.mm"
include "eleq2s.mm"
include "syl5ss.mm"
include "fz0ssnn0.mm"
include "syl6ss.mm"

theorem fzossnn0
  let cM: class M
  let cN: class N


  assert |- ( M e. NN0 -> ( M ..^ N ) C_ NN0 )

  proof
    cM
    cn0
    wcel
    #
    cM
    cN
    cfzo
    co
    #
    cc0
    cN
    cfz
    co
    #
    cn0
    @0
    @1
    cM
    cN
    cfz
    co
    #
    @2
    cM
    cN
    fzossfz
    @3
    @2
    wss
    cM
    cc0
    cuz
    cfv
    cn0
    cM
    cc0
    cN
    fzss1
    nn0uz
    eleq2s
    syl5ss
    cN
    fz0ssnn0
    syl6ss
end
