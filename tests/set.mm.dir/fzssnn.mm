include "cn.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "c1.mm"
include "wss.mm"
include "cuz.mm"
include "cfv.mm"
include "fzss1.mm"
include "nnuz.mm"
include "eleq2s.mm"
include "fzssuz.mm"
include "sseqtr4i.mm"
include "syl6ss.mm"

theorem fzssnn
  let cM: class M
  let cN: class N


  assert |- ( M e. NN -> ( M ... N ) C_ NN )

  proof
    cM
    cn
    wcel
    cM
    cN
    cfz
    co
    #
    c1
    cN
    cfz
    co
    #
    cn
    @0
    @1
    wss
    cM
    c1
    cuz
    cfv
    #
    cn
    cM
    c1
    cN
    fzss1
    nnuz
    eleq2s
    @1
    @2
    cn
    c1
    cN
    fzssuz
    nnuz
    sseqtr4i
    syl6ss
end
