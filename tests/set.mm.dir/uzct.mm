include "cz.mm"
include "cdom.mm"
include "wbr.mm"
include "com.mm"
include "wss.mm"
include "cuz.mm"
include "cfv.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "zex.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "zct.mm"
include "domtr.mm"
include "mp2an.mm"

theorem uzct
  let cN: class N
  let cZ: class Z
  assume uzct.1: |- Z = ( ZZ>= ` N )


  assert |- Z ~<_ _om

  proof
    cZ
    cz
    cdom
    wbr
    #
    cz
    com
    cdom
    wbr
    cZ
    com
    cdom
    wbr
    cZ
    cz
    wss
    #
    @0
    cZ
    cN
    cuz
    cfv
    cz
    uzct.1
    cN
    uzssz
    eqsstri
    cz
    cvv
    wcel
    @1
    @0
    wi
    zex
    cZ
    cz
    cvv
    ssdomg
    ax-mp
    ax-mp
    zct
    cZ
    cz
    com
    domtr
    mp2an
end
