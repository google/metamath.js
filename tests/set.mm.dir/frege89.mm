include "cv.mm"
include "whe.mm"
include "wbr.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "wb.mm"
include "dffrege76.mm"
include "frege52aid.mm"
include "ax-mp.mm"

theorem frege89
  let vw: setvar w
  let cR: class R
  let cU: class U
  let vf: setvar f
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frege89.x: |- X e. U
  assume frege89.y: |- Y e. V
  assume frege89.r: |- R e. W

  disjoint f w
  disjoint R f
  disjoint R w
  disjoint U f
  disjoint V f
  disjoint W f
  disjoint X f
  disjoint X w
  disjoint Y f
  assert |- ( A. f ( R hereditary f -> ( A. w ( X R w -> w e. f ) -> Y e. f ) ) -> X ( t+ ` R ) Y )

  proof
    vf
    cv
    #
    cR
    whe
    cX
    vw
    cv
    cR
    wbr
    vw
    vf
    wel
    wi
    vw
    wal
    cY
    @0
    wcel
    wi
    wi
    vf
    wal
    #
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    #
    wb
    @1
    @2
    wi
    cX
    cR
    cU
    vf
    cY
    cV
    cW
    vw
    frege89.x
    frege89.y
    frege89.r
    dffrege76
    @1
    @2
    frege52aid
    ax-mp
end
