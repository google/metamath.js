include "cv.mm"
include "cpr.mm"
include "weq.mm"
include "wo.mm"
include "cab.mm"
include "cvv.mm"
include "dfpr2.mm"
include "c0.mm"
include "wceq.mm"
include "csn.mm"
include "wa.mm"
include "wex.mm"
include "19.43.mm"
include "prlem2.mm"
include "exbii.mm"
include "0ex.mm"
include "isseti.mm"
include "19.41v.mm"
include "mpbiran.mm"
include "p0ex.mm"
include "orbi12i.mm"
include "3bitr3ri.mm"
include "abbii.mm"
include "pp0ex.mm"
include "eqeltrri.mm"
include "wi.mm"
include "wal.mm"
include "equequ2.mm"
include "0inp0.mm"
include "prlem1.mm"
include "alrimdv.mm"
include "spimev.mm"
include "orcom.mm"
include "con2i.mm"
include "syl7bi.mm"
include "jaoi.mm"
include "zfrep4.mm"
include "eqeltri.mm"

theorem zfpair
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- { x , y } e. _V

  proof
    vx
    cv
    #
    vy
    cv
    #
    cpr
    vw
    vx
    weq
    #
    vw
    vy
    weq
    #
    wo
    #
    vw
    cab
    #
    cvv
    vw
    @0
    @1
    dfpr2
    @5
    vz
    cv
    #
    c0
    wceq
    #
    @6
    c0
    csn
    #
    wceq
    #
    wo
    #
    @7
    @2
    wa
    #
    @9
    @3
    wa
    #
    wo
    #
    wa
    #
    vz
    wex
    #
    vw
    cab
    cvv
    @4
    @15
    vw
    @13
    vz
    wex
    @11
    vz
    wex
    #
    @12
    vz
    wex
    #
    wo
    @15
    @4
    @11
    @12
    vz
    19.43
    @13
    @14
    vz
    @7
    @2
    @9
    @3
    prlem2
    exbii
    @16
    @2
    @17
    @3
    @16
    @7
    vz
    wex
    @2
    vz
    c0
    0ex
    isseti
    @7
    @2
    vz
    19.41v
    mpbiran
    @17
    @9
    vz
    wex
    @3
    vz
    @8
    p0ex
    isseti
    @9
    @3
    vz
    19.41v
    mpbiran
    orbi12i
    3bitr3ri
    abbii
    @10
    @13
    vz
    vw
    vv
    c0
    @8
    cpr
    @10
    vz
    cab
    cvv
    vz
    c0
    @8
    dfpr2
    pp0ex
    eqeltrri
    @7
    @13
    vw
    vv
    weq
    #
    wi
    #
    vw
    wal
    #
    vv
    wex
    @9
    @7
    @20
    vv
    vx
    vv
    vx
    weq
    #
    @7
    @19
    vw
    @21
    @7
    @2
    @9
    @3
    @18
    vv
    vx
    vw
    equequ2
    @6
    0inp0
    #
    prlem1
    alrimdv
    spimev
    @9
    @20
    vv
    vy
    vv
    vy
    weq
    #
    @9
    @19
    vw
    @13
    @12
    @11
    wo
    @23
    @9
    @18
    @11
    @12
    orcom
    @23
    @9
    @3
    @7
    @2
    @18
    vv
    vy
    vw
    equequ2
    @7
    @9
    @22
    con2i
    prlem1
    syl7bi
    alrimdv
    spimev
    jaoi
    zfrep4
    eqeltri
    eqeltri
end
