include "wbr.mm"
include "cv.mm"
include "whe.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "wsbc.mm"
include "frege63c.mm"
include "wb.mm"
include "csb.mm"
include "sbcbr2g.mm"
include "csbvarg.mm"
include "breq2d.mm"
include "bitrd.mm"
include "ax-mp.mm"
include "sbcel1v.mm"
include "imbi2i.mm"
include "3imtr3i.mm"
include "alrimiv.mm"
include "frege90.mm"

theorem frege91
  let cR: class R
  let cU: class U
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vf: setvar f
  assume frege91.x: |- X e. U
  assume frege91.y: |- Y e. V
  assume frege91.r: |- R e. W


  assert |- ( X R Y -> X ( t+ ` R ) Y )

  proof
    cX
    cY
    cR
    wbr
    #
    vf
    cv
    #
    cR
    whe
    #
    cX
    va
    cv
    #
    cR
    wbr
    #
    va
    vf
    wel
    #
    wi
    va
    wal
    #
    cY
    @1
    wcel
    #
    wi
    #
    wi
    #
    vf
    wal
    wi
    @0
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    wi
    @0
    @9
    vf
    @4
    va
    cY
    wsbc
    #
    @2
    @6
    @5
    va
    cY
    wsbc
    #
    wi
    #
    wi
    @0
    @9
    @4
    @2
    @5
    va
    cY
    cV
    frege91.y
    frege63c
    cY
    cV
    wcel
    #
    @10
    @0
    wb
    frege91.y
    @13
    @10
    cX
    va
    cY
    @3
    csb
    #
    cR
    wbr
    @0
    va
    cY
    cX
    @3
    cR
    cV
    sbcbr2g
    @13
    @14
    cY
    cX
    cR
    va
    cY
    cV
    csbvarg
    breq2d
    bitrd
    ax-mp
    @12
    @8
    @2
    @11
    @7
    @6
    va
    cY
    @1
    sbcel1v
    imbi2i
    imbi2i
    3imtr3i
    alrimiv
    @0
    va
    cR
    cU
    vf
    cV
    cW
    cX
    cY
    frege91.x
    frege91.y
    frege91.r
    frege90
    ax-mp
end
