include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "char.mm"
include "cfv.mm"
include "cun.mm"
include "cbs.mm"
include "cabl.mm"
include "cima.mm"
include "c0.mm"
include "wne.mm"
include "con0.mm"
include "harcl.mm"
include "onenon.mm"
include "ax-mp.mm"
include "unnum.mm"
include "mpan2.mm"
include "wss.mm"
include "ssun2.mm"
include "harn0.mm"
include "ssn0.mm"
include "sylancr.mm"
include "isnumbasgrplem3.mm"
include "syl2anc.mm"
include "cgrp.mm"
include "cv.mm"
include "ablgrp.mm"
include "ssriv.mm"
include "imass2.mm"
include "sseli.mm"
include "isnumbasgrplem2.mm"
include "syl.mm"
include "impbii.mm"

theorem isnumbasabl
  let cS: class S
  let vx: setvar x


  assert |- ( S e. dom card <-> ( S u. ( har ` S ) ) e. ( Base " Abel ) )

  proof
    cS
    ccrd
    cdm
    #
    wcel
    #
    cS
    cS
    char
    cfv
    #
    cun
    #
    cbs
    cabl
    cima
    #
    wcel
    #
    @1
    @3
    @0
    wcel
    #
    @3
    c0
    wne
    #
    @5
    @1
    @2
    @0
    wcel
    #
    @6
    @2
    con0
    wcel
    @8
    cS
    harcl
    @2
    onenon
    ax-mp
    cS
    @2
    unnum
    mpan2
    @1
    @2
    @3
    wss
    @2
    c0
    wne
    @7
    @2
    cS
    ssun2
    cS
    @0
    harn0
    @2
    @3
    ssn0
    sylancr
    @3
    isnumbasgrplem3
    syl2anc
    @5
    @3
    cbs
    cgrp
    cima
    #
    wcel
    @1
    @4
    @9
    @3
    cabl
    cgrp
    wss
    @4
    @9
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
    sseli
    cS
    isnumbasgrplem2
    syl
    impbii
end
