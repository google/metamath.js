include "cv.mm"
include "ccsh.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "wrex.mm"
include "cword.mm"
include "crab.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cvv.mm"
include "df-rab.mm"
include "r19.42v.mm"
include "bicomi.mm"
include "abbii.mm"
include "df-rex.mm"
include "3eqtri.mm"
include "abid2.mm"
include "ovex.mm"
include "eqeltri.mm"
include "wtru.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "tru.mm"
include "pm3.2i.mm"
include "ovexd.mm"
include "eqtr3.mm"
include "ex.mm"
include "eqcoms.mm"
include "adantl.mm"
include "com12.mm"
include "ad2antlr.mm"
include "alrimiv.mm"
include "spcimedv.mm"
include "imp.mm"
include "mp1i.mm"
include "zfrep4.mm"

theorem cshwsexa
  let vw: setvar w
  let vn: setvar n
  let cV: class V
  let cW: class W
  let vy: setvar y

  disjoint V n
  disjoint W n
  disjoint W w
  disjoint n w
  disjoint V y
  disjoint n y
  disjoint W y
  disjoint w y
  assert |- { w e. Word V | E. n e. ( 0 ..^ ( # ` W ) ) ( W cyclShift n ) = w } e. _V

  proof
    cW
    vn
    cv
    #
    ccsh
    co
    #
    vw
    cv
    #
    wceq
    #
    vn
    cc0
    cW
    chash
    cfv
    #
    cfzo
    co
    #
    wrex
    #
    vw
    cV
    cword
    #
    crab
    #
    @0
    @5
    wcel
    #
    @2
    @7
    wcel
    #
    @3
    wa
    #
    wa
    vn
    wex
    #
    vw
    cab
    #
    cvv
    @8
    @10
    @6
    wa
    #
    vw
    cab
    @11
    vn
    @5
    wrex
    #
    vw
    cab
    @13
    @6
    vw
    @7
    df-rab
    @14
    @15
    vw
    @15
    @14
    @10
    @3
    vn
    @5
    r19.42v
    bicomi
    abbii
    @15
    @12
    vw
    @11
    vn
    @5
    df-rex
    abbii
    3eqtri
    @9
    @11
    vn
    vw
    vy
    @9
    vn
    cab
    @5
    cvv
    vn
    @5
    abid2
    cc0
    @4
    cfzo
    ovex
    eqeltri
    wtru
    wtru
    wa
    @11
    vw
    vy
    weq
    #
    wi
    #
    vw
    wal
    #
    vy
    wex
    #
    @9
    wtru
    wtru
    tru
    tru
    pm3.2i
    wtru
    wtru
    @19
    wtru
    @18
    wtru
    vy
    @1
    cvv
    wtru
    cW
    @0
    ccsh
    ovexd
    wtru
    vy
    cv
    #
    @1
    wceq
    #
    wa
    #
    wtru
    @18
    @22
    wtru
    wa
    @17
    vw
    @21
    @17
    wtru
    wtru
    @11
    @21
    @16
    @3
    @21
    @16
    wi
    #
    @10
    @23
    @2
    @1
    @2
    @1
    wceq
    @21
    @16
    @2
    @20
    @1
    eqtr3
    ex
    eqcoms
    adantl
    com12
    ad2antlr
    alrimiv
    ex
    spcimedv
    imp
    mp1i
    zfrep4
    eqeltri
end
