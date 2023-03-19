include "cv.mm"
include "wbr.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "whe.mm"
include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "wsbc.mm"
include "cvv.mm"
include "vex.mm"
include "frege60c.mm"
include "sbcid.mm"
include "imbi12i.mm"
include "3imtr3g.mm"
include "axc4i.mm"
include "frege90.mm"
include "ax-mp.mm"

theorem frege93
  let vz: setvar z
  let cR: class R
  let cU: class U
  let vf: setvar f
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frege91.x: |- X e. U
  assume frege91.y: |- Y e. V
  assume frege91.r: |- R e. W

  disjoint f z
  disjoint R f
  disjoint R z
  disjoint U f
  disjoint V f
  disjoint W f
  disjoint X f
  disjoint X z
  disjoint Y f
  assert |- ( A. f ( A. z ( X R z -> z e. f ) -> ( R hereditary f -> Y e. f ) ) -> X ( t+ ` R ) Y )

  proof
    cX
    vz
    cv
    cR
    wbr
    vz
    vf
    wel
    wi
    vz
    wal
    #
    vf
    cv
    #
    cR
    whe
    #
    cY
    @1
    wcel
    #
    wi
    wi
    #
    vf
    wal
    #
    @2
    @0
    @3
    wi
    #
    wi
    #
    vf
    wal
    wi
    @5
    cX
    cY
    cR
    ctcl
    cfv
    wbr
    wi
    @4
    @7
    vf
    @5
    @2
    vf
    @1
    wsbc
    @0
    vf
    @1
    wsbc
    #
    @3
    vf
    @1
    wsbc
    #
    wi
    @2
    @6
    @0
    @2
    @3
    vf
    @1
    cvv
    vf
    vex
    frege60c
    @2
    vf
    sbcid
    @8
    @0
    @9
    @3
    @0
    vf
    sbcid
    @3
    vf
    sbcid
    imbi12i
    3imtr3g
    axc4i
    @5
    vz
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
