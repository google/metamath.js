include "cfz.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "wss.mm"
include "clt.mm"
include "wwe.mm"
include "fzssuz.mm"
include "ltweuz.mm"
include "wess.mm"
include "mp2.mm"

theorem ltwefz
  let cM: class M
  let cN: class N


  assert |- < We ( M ... N )

  proof
    cM
    cN
    cfz
    co
    #
    cM
    cuz
    cfv
    #
    wss
    @1
    clt
    wwe
    @0
    clt
    wwe
    cM
    cN
    fzssuz
    cM
    ltweuz
    @0
    @1
    clt
    wess
    mp2
end
