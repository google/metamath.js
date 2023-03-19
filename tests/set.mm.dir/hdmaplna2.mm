include "co.mm"
include "cfv.mm"
include "clcd.mm"
include "cplusg.mm"
include "eqid.mm"
include "hdmapadd.mm"
include "fveq1d.mm"
include "cbs.mm"
include "hdmapcl.mm"
include "lcdvaddval.mm"
include "eqtrd.mm"

theorem hdmaplna2
  let wph: wff ph
  let c.pl: class .+
  let c.pd: class .+^
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume hdmaplna2.h: |- H = ( LHyp ` K )
  assume hdmaplna2.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmaplna2.v: |- V = ( Base ` U )
  assume hdmaplna2.p: |- .+ = ( +g ` U )
  assume hdmaplna2.r: |- R = ( Scalar ` U )
  assume hdmaplna2.q: |- .+^ = ( +g ` R )
  assume hdmaplna2.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaplna2.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmaplna2.x: |- ( ph -> X e. V )
  assume hdmaplna2.y: |- ( ph -> Y e. V )
  assume hdmaplna2.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( ( S ` ( Y .+ Z ) ) ` X ) = ( ( ( S ` Y ) ` X ) .+^ ( ( S ` Z ) ` X ) ) )

  proof
    wph
    cX
    cY
    cZ
    c.pl
    co
    cS
    cfv
    #
    cfv
    cX
    cY
    cS
    cfv
    #
    cZ
    cS
    cfv
    #
    cW
    cK
    clcd
    cfv
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cfv
    cX
    @1
    cfv
    cX
    @2
    cfv
    c.pd
    co
    wph
    cX
    @0
    @5
    wph
    @3
    c.pl
    @4
    cS
    cU
    cH
    cK
    cV
    cW
    cY
    cZ
    hdmaplna2.h
    hdmaplna2.u
    hdmaplna2.v
    hdmaplna2.p
    @3
    eqid
    #
    @4
    eqid
    #
    hdmaplna2.s
    hdmaplna2.k
    hdmaplna2.y
    hdmaplna2.z
    hdmapadd
    fveq1d
    wph
    @3
    @3
    cbs
    cfv
    #
    c.pd
    @4
    cR
    cU
    @1
    @2
    cH
    cK
    cV
    cW
    cX
    hdmaplna2.h
    hdmaplna2.u
    hdmaplna2.v
    hdmaplna2.r
    hdmaplna2.q
    @6
    @8
    eqid
    #
    @7
    hdmaplna2.k
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
    hdmaplna2.h
    hdmaplna2.u
    hdmaplna2.v
    @6
    @9
    hdmaplna2.s
    hdmaplna2.k
    hdmaplna2.y
    hdmapcl
    wph
    @3
    @8
    cS
    cZ
    cU
    cH
    cK
    cV
    cW
    hdmaplna2.h
    hdmaplna2.u
    hdmaplna2.v
    @6
    @9
    hdmaplna2.s
    hdmaplna2.k
    hdmaplna2.z
    hdmapcl
    hdmaplna2.x
    lcdvaddval
    eqtrd
end
