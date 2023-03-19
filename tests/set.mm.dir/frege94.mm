include "cv.mm"
include "wbr.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "frege93.mm"
include "frege7.mm"
include "ax-mp.mm"

theorem frege94
  let vw: setvar w
  let cR: class R
  let cU: class U
  let vf: setvar f
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume frege94.x: |- X e. U
  assume frege94.z: |- Z e. V
  assume frege94.r: |- R e. W

  disjoint f w
  disjoint R f
  disjoint R w
  disjoint U f
  disjoint V f
  disjoint W f
  disjoint X f
  disjoint X w
  disjoint Z f
  assert |- ( ( Y R Z -> ( X ( t+ ` R ) Y -> A. f ( A. w ( X R w -> w e. f ) -> ( R hereditary f -> Z e. f ) ) ) ) -> ( Y R Z -> ( X ( t+ ` R ) Y -> X ( t+ ` R ) Z ) ) )

  proof
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
    vf
    cv
    #
    cR
    whe
    cZ
    @0
    wcel
    wi
    wi
    vf
    wal
    #
    cX
    cZ
    cR
    ctcl
    cfv
    #
    wbr
    #
    wi
    cY
    cZ
    cR
    wbr
    #
    cX
    cY
    @2
    wbr
    #
    @1
    wi
    wi
    @4
    @5
    @3
    wi
    wi
    wi
    vw
    cR
    cU
    vf
    cV
    cW
    cX
    cZ
    frege94.x
    frege94.z
    frege94.r
    frege93
    @1
    @3
    @4
    @5
    frege7
    ax-mp
end
