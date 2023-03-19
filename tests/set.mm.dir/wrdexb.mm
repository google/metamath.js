include "cvv.mm"
include "wcel.mm"
include "cword.mm"
include "wrdexg.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "cc0.mm"
include "cop.mm"
include "wa.mm"
include "csn.mm"
include "opex.mm"
include "snid.mm"
include "snopiswrd.mm"
include "elunii.mm"
include "sylancr.mm"
include "c0ex.mm"
include "vex.mm"
include "opeluu.mm"
include "syl.mm"
include "simprd.mm"
include "ssriv.mm"
include "uniexg.mm"
include "3syl.mm"
include "ssexg.mm"
include "impbii.mm"

theorem wrdexb
  let cS: class S
  let vl: setvar l
  let vs: setvar s
  let cV: class V


  assert |- ( S e. _V <-> Word S e. _V )

  proof
    cS
    cvv
    wcel
    #
    cS
    cword
    #
    cvv
    wcel
    #
    cS
    cvv
    wrdexg
    @2
    cS
    @1
    cuni
    #
    cuni
    #
    cuni
    #
    wss
    @5
    cvv
    wcel
    #
    @0
    vs
    cS
    @5
    vs
    cv
    #
    cS
    wcel
    #
    cc0
    @5
    wcel
    #
    @7
    @5
    wcel
    #
    @8
    cc0
    @7
    cop
    #
    @3
    wcel
    #
    @9
    @10
    wa
    @8
    @11
    @11
    csn
    #
    wcel
    @13
    @1
    wcel
    @12
    @11
    cc0
    @7
    opex
    snid
    @7
    cS
    snopiswrd
    @11
    @13
    @1
    elunii
    sylancr
    cc0
    @7
    @3
    c0ex
    vs
    vex
    opeluu
    syl
    simprd
    ssriv
    @2
    @3
    cvv
    wcel
    @4
    cvv
    wcel
    @6
    @1
    cvv
    uniexg
    @3
    cvv
    uniexg
    @4
    cvv
    uniexg
    3syl
    cS
    @5
    cvv
    ssexg
    sylancr
    impbii
end
