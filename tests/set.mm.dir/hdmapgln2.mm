include "co.mm"
include "cfv.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "hdmaplna2.mm"
include "hdmapglnm2.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem hdmapgln2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume hdmapgln2.h: |- H = ( LHyp ` K )
  assume hdmapgln2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapgln2.v: |- V = ( Base ` U )
  assume hdmapgln2.p: |- .+ = ( +g ` U )
  assume hdmapgln2.t: |- .x. = ( .s ` U )
  assume hdmapgln2.r: |- R = ( Scalar ` U )
  assume hdmapgln2.b: |- B = ( Base ` R )
  assume hdmapgln2.q: |- .+^ = ( +g ` R )
  assume hdmapgln2.m: |- .X. = ( .r ` R )
  assume hdmapgln2.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapgln2.g: |- G = ( ( HGMap ` K ) ` W )
  assume hdmapgln2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapgln2.x: |- ( ph -> X e. V )
  assume hdmapgln2.y: |- ( ph -> Y e. V )
  assume hdmapgln2.z: |- ( ph -> Z e. V )
  assume hdmapgln2.a: |- ( ph -> A e. B )


  assert |- ( ph -> ( ( S ` ( ( A .x. Y ) .+ Z ) ) ` X ) = ( ( ( ( S ` Y ) ` X ) .X. ( G ` A ) ) .+^ ( ( S ` Z ) ` X ) ) )

  proof
    wph
    cX
    cA
    cY
    c.x
    co
    #
    cZ
    c.pl
    co
    cS
    cfv
    cfv
    cX
    @0
    cS
    cfv
    cfv
    #
    cX
    cZ
    cS
    cfv
    cfv
    #
    c.pd
    co
    cX
    cY
    cS
    cfv
    cfv
    cA
    cG
    cfv
    c.xp
    co
    #
    @2
    c.pd
    co
    wph
    c.pl
    c.pd
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    cX
    @0
    cZ
    hdmapgln2.h
    hdmapgln2.u
    hdmapgln2.v
    hdmapgln2.p
    hdmapgln2.r
    hdmapgln2.q
    hdmapgln2.s
    hdmapgln2.k
    hdmapgln2.x
    wph
    cU
    clmod
    wcel
    cA
    cB
    wcel
    cY
    cV
    wcel
    @0
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmapgln2.h
    hdmapgln2.u
    hdmapgln2.k
    dvhlmod
    hdmapgln2.a
    hdmapgln2.y
    cA
    c.x
    cR
    cB
    cV
    cU
    cY
    hdmapgln2.v
    hdmapgln2.r
    hdmapgln2.t
    hdmapgln2.b
    lmodvscl
    syl3anc
    hdmapgln2.z
    hdmaplna2
    wph
    @1
    @3
    @2
    c.pd
    wph
    cA
    cB
    cR
    cS
    c.x
    c.xp
    cU
    cG
    cH
    cK
    cV
    cW
    cX
    cY
    hdmapgln2.h
    hdmapgln2.u
    hdmapgln2.v
    hdmapgln2.t
    hdmapgln2.r
    hdmapgln2.b
    hdmapgln2.m
    hdmapgln2.s
    hdmapgln2.g
    hdmapgln2.k
    hdmapgln2.x
    hdmapgln2.y
    hdmapgln2.a
    hdmapglnm2
    oveq1d
    eqtrd
end
