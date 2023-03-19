include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "cwdom.mm"
include "wbr.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wi.mm"
include "relwdom.mm"
include "brrelex2i.mm"
include "a1i.mm"
include "cdm.mm"
include "wf.mm"
include "wceq.mm"
include "fof.mm"
include "fdm.mm"
include "syl.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "exlimiv.mm"
include "wb.mm"
include "wo.mm"
include "brwdom.mm"
include "wn.mm"
include "df-ne.mm"
include "biorf.mm"
include "sylbi.mm"
include "bicomd.mm"
include "sylan9bbr.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem brwdomn0
  let vz: setvar z
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
  assert |- ( X =/= (/) -> ( X ~<_* Y <-> E. z z : Y -onto-> X ) )

  proof
    cX
    c0
    wne
    #
    cY
    cvv
    wcel
    #
    cX
    cY
    cwdom
    wbr
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
    @2
    @1
    wi
    @0
    cX
    cY
    cwdom
    relwdom
    brrelex2i
    a1i
    @5
    @1
    wi
    @0
    @4
    @1
    vz
    @4
    cY
    @3
    cdm
    #
    cvv
    @4
    cY
    cX
    @3
    wf
    @6
    cY
    wceq
    cY
    cX
    @3
    fof
    cY
    cX
    @3
    fdm
    syl
    @3
    vz
    vex
    dmex
    syl6eqelr
    exlimiv
    a1i
    @0
    @1
    @2
    @5
    wb
    @1
    @2
    cX
    c0
    wceq
    #
    @5
    wo
    #
    @0
    @5
    vz
    cvv
    cX
    cY
    brwdom
    @0
    @5
    @8
    @0
    @7
    wn
    @5
    @8
    wb
    cX
    c0
    df-ne
    @7
    @5
    biorf
    sylbi
    bicomd
    sylan9bbr
    ex
    pm5.21ndd
end
