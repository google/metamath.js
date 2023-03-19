include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "char.mm"
include "cfv.mm"
include "cun.mm"
include "cbs.mm"
include "cgrp.mm"
include "cima.mm"
include "cabl.mm"
include "wss.mm"
include "cv.mm"
include "ablgrp.mm"
include "ssriv.mm"
include "imass2.mm"
include "ax-mp.mm"
include "isnumbasabl.mm"
include "biimpi.mm"
include "sseldi.mm"
include "isnumbasgrplem2.mm"
include "impbii.mm"

theorem isnumbasgrp
  let cS: class S
  let vx: setvar x


  assert |- ( S e. dom card <-> ( S u. ( har ` S ) ) e. ( Base " Grp ) )

  proof
    cS
    ccrd
    cdm
    wcel
    #
    cS
    cS
    char
    cfv
    cun
    #
    cbs
    cgrp
    cima
    #
    wcel
    @0
    cbs
    cabl
    cima
    #
    @2
    @1
    cabl
    cgrp
    wss
    @3
    @2
    wss
    vx
    cabl
    cgrp
    vx
    cv
    ablgrp
    ssriv
    cabl
    cgrp
    cbs
    imass2
    ax-mp
    @0
    @1
    @3
    wcel
    cS
    isnumbasabl
    biimpi
    sseldi
    cS
    isnumbasgrplem2
    impbii
end
