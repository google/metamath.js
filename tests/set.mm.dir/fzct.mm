include "cfz.mm"
include "co.mm"
include "cz.mm"
include "wss.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "fzssz.mm"
include "zct.mm"
include "ssct.mm"
include "mp2an.mm"

theorem fzct
  let cM: class M
  let cN: class N


  assert |- ( N ... M ) ~<_ _om

  proof
    cN
    cM
    cfz
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
    fzssz
    zct
    @0
    cz
    ssct
    mp2an
end
