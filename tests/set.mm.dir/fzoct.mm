include "cfzo.mm"
include "co.mm"
include "cz.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "fzossz.mm"
include "zct.mm"
include "ssct.mm"
include "mp2an.mm"

theorem fzoct
  let cM: class M
  let cN: class N


  assert |- ( N ..^ M ) ~<_ _om

  proof
    cN
    cM
    cfzo
    co
    #
    cz
    wss
    cz
    com
    cdom
    wbr
    @0
    com
    cdom
    wbr
    cN
    cM
    fzossz
    zct
    @0
    cz
    ssct
    mp2an
end
