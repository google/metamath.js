include "cprime.mm"
include "cn.mm"
include "nnex.mm"
include "prmssnn.mm"
include "ssexi.mm"

theorem prmex



  assert |- Prime e. _V

  proof
    cprime
    cn
    nnex
    prmssnn
    ssexi
end
