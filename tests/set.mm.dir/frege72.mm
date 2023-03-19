include "cv.mm"
include "wbr.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "wsbc.mm"
include "frege58c.mm"
include "sbcim1.mm"
include "wb.mm"
include "csb.mm"
include "sbcbr2g.mm"
include "csbvarg.mm"
include "breq2d.mm"
include "bitrd.mm"
include "ax-mp.mm"
include "sbcel1v.mm"
include "3imtr3g.mm"
include "syl.mm"
include "frege71.mm"

theorem frege72
  let cA: class A
  let cR: class R
  let cU: class U
  let cV: class V
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume frege72.x: |- X e. U
  assume frege72.y: |- Y e. V


  assert |- ( R hereditary A -> ( X e. A -> ( X R Y -> Y e. A ) ) )

  proof
    cX
    vz
    cv
    #
    cR
    wbr
    #
    @0
    cA
    wcel
    #
    wi
    #
    vz
    wal
    #
    cX
    cY
    cR
    wbr
    #
    cY
    cA
    wcel
    #
    wi
    #
    wi
    cA
    cR
    whe
    cX
    cA
    wcel
    @7
    wi
    wi
    @4
    @3
    vz
    cY
    wsbc
    #
    @7
    @3
    vz
    cY
    cV
    frege72.y
    frege58c
    @8
    @1
    vz
    cY
    wsbc
    #
    @2
    vz
    cY
    wsbc
    @5
    @6
    @1
    @2
    vz
    cY
    sbcim1
    cY
    cV
    wcel
    #
    @9
    @5
    wb
    frege72.y
    @10
    @9
    cX
    vz
    cY
    @0
    csb
    #
    cR
    wbr
    @5
    vz
    cY
    cX
    @0
    cR
    cV
    sbcbr2g
    @10
    @11
    cY
    cX
    cR
    vz
    cY
    cV
    csbvarg
    breq2d
    bitrd
    ax-mp
    vz
    cY
    cA
    sbcel1v
    3imtr3g
    syl
    vz
    cA
    cR
    cU
    cX
    cY
    frege72.x
    frege71
    ax-mp
end
