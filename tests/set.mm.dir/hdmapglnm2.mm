include "co.mm"
include "cfv.mm"
include "clcd.mm"
include "cvsca.mm"
include "eqid.mm"
include "hgmapvs.mm"
include "fveq1d.mm"
include "cbs.mm"
include "hgmapcl.mm"
include "hdmapcl.mm"
include "lcdvsval.mm"
include "eqtrd.mm"

theorem hdmapglnm2
  let wph: wff ph
  let cA: class A
  let cB: class B
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
  assume hdmapglnm2.h: |- H = ( LHyp ` K )
  assume hdmapglnm2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapglnm2.v: |- V = ( Base ` U )
  assume hdmapglnm2.t: |- .x. = ( .s ` U )
  assume hdmapglnm2.r: |- R = ( Scalar ` U )
  assume hdmapglnm2.b: |- B = ( Base ` R )
  assume hdmapglnm2.m: |- .X. = ( .r ` R )
  assume hdmapglnm2.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapglnm2.g: |- G = ( ( HGMap ` K ) ` W )
  assume hdmapglnm2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapglnm2.x: |- ( ph -> X e. V )
  assume hdmapglnm2.y: |- ( ph -> Y e. V )
  assume hdmapglnm2.z: |- ( ph -> A e. B )


  assert |- ( ph -> ( ( S ` ( A .x. Y ) ) ` X ) = ( ( ( S ` Y ) ` X ) .X. ( G ` A ) ) )

  proof
    wph
    cX
    cA
    cY
    c.x
    co
    cS
    cfv
    #
    cfv
    cX
    cA
    cG
    cfv
    #
    cY
    cS
    cfv
    #
    cW
    cK
    clcd
    cfv
    cfv
    #
    cvsca
    cfv
    #
    co
    #
    cfv
    cX
    @2
    cfv
    @1
    c.xp
    co
    wph
    cX
    @0
    @5
    wph
    cB
    @3
    cR
    cS
    @4
    c.x
    cU
    cA
    cG
    cH
    cK
    cV
    cW
    cY
    hdmapglnm2.h
    hdmapglnm2.u
    hdmapglnm2.v
    hdmapglnm2.t
    hdmapglnm2.r
    hdmapglnm2.b
    @3
    eqid
    #
    @4
    eqid
    #
    hdmapglnm2.s
    hdmapglnm2.g
    hdmapglnm2.k
    hdmapglnm2.y
    hdmapglnm2.z
    hgmapvs
    fveq1d
    wph
    cX
    @3
    cB
    cR
    @4
    c.xp
    cU
    @3
    cbs
    cfv
    #
    @2
    cH
    cK
    cV
    cW
    @1
    hdmapglnm2.h
    hdmapglnm2.u
    hdmapglnm2.v
    hdmapglnm2.r
    hdmapglnm2.b
    hdmapglnm2.m
    @6
    @8
    eqid
    #
    @7
    hdmapglnm2.k
    wph
    cB
    cR
    cU
    cA
    cG
    cH
    cK
    cW
    hdmapglnm2.h
    hdmapglnm2.u
    hdmapglnm2.r
    hdmapglnm2.b
    hdmapglnm2.g
    hdmapglnm2.k
    hdmapglnm2.z
    hgmapcl
    wph
    @3
    @8
    cS
    cY
    cU
    cH
    cK
    cV
    cW
    hdmapglnm2.h
    hdmapglnm2.u
    hdmapglnm2.v
    @6
    @9
    hdmapglnm2.s
    hdmapglnm2.k
    hdmapglnm2.y
    hdmapcl
    hdmapglnm2.x
    lcdvsval
    eqtrd
end
