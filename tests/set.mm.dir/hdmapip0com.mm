include "csn.mm"
include "coch.mm"
include "cfv.mm"
include "wcel.mm"
include "wceq.mm"
include "eqid.mm"
include "dochsncom.mm"
include "hdmapellkr.mm"
include "3bitr4d.mm"

theorem hdmapip0com
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume hdmapip0com.h: |- H = ( LHyp ` K )
  assume hdmapip0com.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapip0com.v: |- V = ( Base ` U )
  assume hdmapip0com.r: |- R = ( Scalar ` U )
  assume hdmapip0com.z: |- .0. = ( 0g ` R )
  assume hdmapip0com.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapip0com.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapip0com.x: |- ( ph -> X e. V )
  assume hdmapip0com.y: |- ( ph -> Y e. V )


  assert |- ( ph -> ( ( ( S ` X ) ` Y ) = .0. <-> ( ( S ` Y ) ` X ) = .0. ) )

  proof
    wph
    cY
    cX
    csn
    cW
    cK
    coch
    cfv
    cfv
    #
    cfv
    wcel
    cX
    cY
    csn
    @0
    cfv
    wcel
    cY
    cX
    cS
    cfv
    cfv
    c.0
    wceq
    cX
    cY
    cS
    cfv
    cfv
    c.0
    wceq
    wph
    cU
    cH
    cK
    @0
    cV
    cW
    cY
    cX
    hdmapip0com.h
    @0
    eqid
    #
    hdmapip0com.u
    hdmapip0com.v
    hdmapip0com.k
    hdmapip0com.y
    hdmapip0com.x
    dochsncom
    wph
    cR
    cS
    cU
    cH
    cK
    @0
    cV
    cW
    cX
    cY
    c.0
    hdmapip0com.h
    @1
    hdmapip0com.u
    hdmapip0com.v
    hdmapip0com.r
    hdmapip0com.z
    hdmapip0com.s
    hdmapip0com.k
    hdmapip0com.x
    hdmapip0com.y
    hdmapellkr
    wph
    cR
    cS
    cU
    cH
    cK
    @0
    cV
    cW
    cY
    cX
    c.0
    hdmapip0com.h
    @1
    hdmapip0com.u
    hdmapip0com.v
    hdmapip0com.r
    hdmapip0com.z
    hdmapip0com.s
    hdmapip0com.k
    hdmapip0com.y
    hdmapip0com.x
    hdmapellkr
    3bitr4d
end
