include "wcel.mm"
include "cvv.mm"
include "cwdom.mm"
include "wbr.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wo.mm"
include "wb.mm"
include "elex.mm"
include "wi.mm"
include "relwdom.mm"
include "brrelexi.mm"
include "a1i.mm"
include "0ex.mm"
include "eleq1a.mm"
include "ax-mp.mm"
include "crn.mm"
include "forn.mm"
include "vex.mm"
include "rnex.mm"
include "syl6eqelr.mm"
include "exlimiv.mm"
include "jaoi.mm"
include "eqeq1.mm"
include "foeq3.mm"
include "exbidv.mm"
include "orbi12d.mm"
include "foeq2.mm"
include "orbi2d.mm"
include "df-wdom.mm"
include "brabg.mm"
include "expcom.mm"
include "pm5.21ndd.mm"
include "syl.mm"

theorem brwdom
  let vz: setvar z
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cF: class F
  let cZ: class Z

  disjoint X z
  disjoint Y z
  disjoint X x
  disjoint X y
  disjoint X w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint Y x
  disjoint Y y
  disjoint Y w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint Z w
  assert |- ( Y e. V -> ( X ~<_* Y <-> ( X = (/) \/ E. z z : Y -onto-> X ) ) )

  proof
    cY
    cV
    wcel
    cY
    cvv
    wcel
    #
    cX
    cY
    cwdom
    wbr
    #
    cX
    c0
    wceq
    #
    cY
    cX
    vz
    cv
    #
    wfo
    #
    vz
    wex
    #
    wo
    #
    wb
    #
    cY
    cV
    elex
    @0
    cX
    cvv
    wcel
    #
    @1
    @6
    @1
    @8
    wi
    @0
    cX
    cY
    cwdom
    relwdom
    brrelexi
    a1i
    @6
    @8
    wi
    @0
    @2
    @8
    @5
    c0
    cvv
    wcel
    @2
    @8
    wi
    0ex
    c0
    cvv
    cX
    eleq1a
    ax-mp
    @4
    @8
    vz
    @4
    cX
    @3
    crn
    cvv
    cY
    cX
    @3
    forn
    @3
    vz
    vex
    rnex
    syl6eqelr
    exlimiv
    jaoi
    a1i
    @8
    @0
    @7
    vx
    cv
    #
    c0
    wceq
    #
    vy
    cv
    #
    @9
    @3
    wfo
    #
    vz
    wex
    #
    wo
    @2
    @11
    cX
    @3
    wfo
    #
    vz
    wex
    #
    wo
    @6
    vx
    vy
    cX
    cY
    cvv
    cvv
    cwdom
    @9
    cX
    wceq
    #
    @10
    @2
    @13
    @15
    @9
    cX
    c0
    eqeq1
    @16
    @12
    @14
    vz
    @9
    cX
    @11
    @3
    foeq3
    exbidv
    orbi12d
    @11
    cY
    wceq
    #
    @15
    @5
    @2
    @17
    @14
    @4
    vz
    @11
    cY
    cX
    @3
    foeq2
    exbidv
    orbi2d
    vx
    vy
    vz
    df-wdom
    brabg
    expcom
    pm5.21ndd
    syl
end
