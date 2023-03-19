include "cwdom.mm"
include "wbr.mm"
include "wa.mm"
include "c0.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "wi.mm"
include "relwdom.mm"
include "brrelex2i.mm"
include "adantl.mm"
include "0wdom.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "syl.mm"
include "wne.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "simpll.mm"
include "wb.mm"
include "brwdomn0.mm"
include "mpbid.mm"
include "simpllr.mm"
include "simplr.mm"
include "cdm.mm"
include "crn.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "a1i.mm"
include "wf.mm"
include "fof.mm"
include "fdm.mm"
include "neeq1d.mm"
include "forn.mm"
include "3bitr3rd.mm"
include "ccom.mm"
include "vex.mm"
include "coex.mm"
include "foco.mm"
include "fowdom.mm"
include "sylancr.mm"
include "expr.mm"
include "exlimdv.mm"
include "mpd.mm"
include "exlimddv.mm"
include "ex.mm"
include "pm2.61dne.mm"

theorem wdomtr
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cF: class F


  assert |- ( ( X ~<_* Y /\ Y ~<_* Z ) -> X ~<_* Z )

  proof
    cX
    cY
    cwdom
    wbr
    #
    cY
    cZ
    cwdom
    wbr
    #
    wa
    #
    cX
    cZ
    cwdom
    wbr
    #
    cX
    c0
    @2
    cZ
    cvv
    wcel
    #
    cX
    c0
    wceq
    #
    @3
    wi
    @1
    @4
    @0
    cY
    cZ
    cwdom
    relwdom
    brrelex2i
    adantl
    @4
    @3
    @5
    c0
    cZ
    cwdom
    wbr
    cvv
    cZ
    0wdom
    cX
    c0
    cZ
    cwdom
    breq1
    syl5ibrcom
    syl
    @2
    cX
    c0
    wne
    #
    @3
    @2
    @6
    wa
    #
    cY
    cX
    vz
    cv
    #
    wfo
    #
    @3
    vz
    @7
    @0
    @9
    vz
    wex
    #
    @0
    @1
    @6
    simpll
    @6
    @0
    @10
    wb
    @2
    vz
    cX
    cY
    brwdomn0
    adantl
    mpbid
    @7
    @9
    wa
    #
    cZ
    cY
    vy
    cv
    #
    wfo
    #
    vy
    wex
    #
    @3
    @11
    @1
    @14
    @0
    @1
    @6
    @9
    simpllr
    @11
    cY
    c0
    wne
    #
    @1
    @14
    wb
    @11
    @6
    @15
    @2
    @6
    @9
    simplr
    @9
    @6
    @15
    wb
    @7
    @9
    @8
    cdm
    #
    c0
    wne
    #
    @8
    crn
    #
    c0
    wne
    #
    @15
    @6
    @17
    @19
    wb
    @9
    @16
    c0
    @18
    c0
    @8
    dm0rn0
    necon3bii
    a1i
    @9
    @16
    cY
    c0
    @9
    cY
    cX
    @8
    wf
    @16
    cY
    wceq
    cY
    cX
    @8
    fof
    cY
    cX
    @8
    fdm
    syl
    neeq1d
    @9
    @18
    cX
    c0
    cY
    cX
    @8
    forn
    neeq1d
    3bitr3rd
    adantl
    mpbid
    vy
    cY
    cZ
    brwdomn0
    syl
    mpbid
    @11
    @13
    @3
    vy
    @7
    @9
    @13
    @3
    @9
    @13
    wa
    #
    @3
    @7
    @20
    @8
    @12
    ccom
    #
    cvv
    wcel
    cZ
    cX
    @21
    wfo
    @3
    @8
    @12
    vz
    vex
    vy
    vex
    coex
    cZ
    cY
    cX
    @8
    @12
    foco
    @21
    cvv
    cX
    cZ
    fowdom
    sylancr
    adantl
    expr
    exlimdv
    mpd
    exlimddv
    ex
    pm2.61dne
end
