include "cv.mm"
include "whe.mm"
include "wbr.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "wcel.mm"
include "ctcl.mm"
include "cfv.mm"
include "frege89.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege90
  let wph: wff ph
  let vw: setvar w
  let cR: class R
  let cU: class U
  let vf: setvar f
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume frege90.x: |- X e. U
  assume frege90.y: |- Y e. V
  assume frege90.r: |- R e. W

  disjoint f w
  disjoint R f
  disjoint R w
  disjoint U f
  disjoint V f
  disjoint W f
  disjoint X f
  disjoint X w
  disjoint Y f
  assert |- ( ( ph -> A. f ( R hereditary f -> ( A. w ( X R w -> w e. f ) -> Y e. f ) ) ) -> ( ph -> X ( t+ ` R ) Y ) )

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
    wi
    wph
    @1
    wi
    wph
    @2
    wi
    wi
    vw
    cR
    cU
    vf
    cV
    cW
    cX
    cY
    frege90.x
    frege90.y
    frege90.r
    frege89
    @1
    @2
    wph
    frege5
    ax-mp
end
