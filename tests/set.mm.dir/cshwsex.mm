include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "ccsh.mm"
include "csn.mm"
include "ciun.mm"
include "cvv.mm"
include "cshwsiun.mm"
include "wral.mm"
include "ovex.mm"
include "snex.mm"
include "a1i.mm"
include "ralrimivw.mm"
include "iunexg.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem cshwsex
  let vw: setvar w
  let vn: setvar n
  let cM: class M
  let cV: class V
  let cW: class W
  assume cshwrepswhash1.m: |- M = { w e. Word V | E. n e. ( 0 ..^ ( # ` W ) ) ( W cyclShift n ) = w }

  disjoint V n
  disjoint V w
  disjoint n w
  disjoint W n
  disjoint W w
  assert |- ( W e. Word V -> M e. _V )

  proof
    cW
    cV
    cword
    wcel
    #
    cM
    vn
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    cW
    vn
    cv
    ccsh
    co
    #
    csn
    #
    ciun
    #
    cvv
    vw
    vn
    cM
    cV
    cW
    cshwrepswhash1.m
    cshwsiun
    @0
    @2
    cvv
    wcel
    @4
    cvv
    wcel
    #
    vn
    @2
    wral
    @5
    cvv
    wcel
    cc0
    @1
    cfzo
    ovex
    @0
    @6
    vn
    @2
    @6
    @0
    @3
    snex
    a1i
    ralrimivw
    vn
    @2
    @4
    cvv
    cvv
    iunexg
    sylancr
    eqeltrd
end
