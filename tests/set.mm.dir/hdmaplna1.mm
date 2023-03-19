include "clmod.mm"
include "wcel.mm"
include "cfv.mm"
include "clfn.mm"
include "co.mm"
include "wceq.mm"
include "dvhlmod.mm"
include "clcd.mm"
include "cbs.mm"
include "eqid.mm"
include "hdmapcl.mm"
include "lcdvbaselfl.mm"
include "lfladd.mm"
include "syl112anc.mm"

theorem hdmaplna1
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
  assume hdmaplna1.h: |- H = ( LHyp ` K )
  assume hdmaplna1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmaplna1.v: |- V = ( Base ` U )
  assume hdmaplna1.p: |- .+ = ( +g ` U )
  assume hdmaplna1.r: |- R = ( Scalar ` U )
  assume hdmaplna1.q: |- .+^ = ( +g ` R )
  assume hdmaplna1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaplna1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmaplna1.x: |- ( ph -> X e. V )
  assume hdmaplna1.y: |- ( ph -> Y e. V )
  assume hdmaplna1.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( ( S ` Z ) ` ( X .+ Y ) ) = ( ( ( S ` Z ) ` X ) .+^ ( ( S ` Z ) ` Y ) ) )

  proof
    wph
    cU
    clmod
    wcel
    cZ
    cS
    cfv
    #
    cU
    clfn
    cfv
    #
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    cX
    cY
    c.pl
    co
    @0
    cfv
    cX
    @0
    cfv
    cY
    @0
    cfv
    c.pd
    co
    wceq
    wph
    cU
    cH
    cK
    cW
    hdmaplna1.h
    hdmaplna1.u
    hdmaplna1.k
    dvhlmod
    wph
    cW
    cK
    clcd
    cfv
    cfv
    #
    cU
    @1
    cH
    cK
    @2
    cbs
    cfv
    #
    cW
    @0
    hdmaplna1.h
    @2
    eqid
    #
    @3
    eqid
    #
    hdmaplna1.u
    @1
    eqid
    #
    hdmaplna1.k
    wph
    @2
    @3
    cS
    cZ
    cU
    cH
    cK
    cV
    cW
    hdmaplna1.h
    hdmaplna1.u
    hdmaplna1.v
    @4
    @5
    hdmaplna1.s
    hdmaplna1.k
    hdmaplna1.z
    hdmapcl
    lcdvbaselfl
    hdmaplna1.x
    hdmaplna1.y
    cR
    c.pl
    c.pd
    @1
    @0
    cV
    cU
    cX
    cY
    hdmaplna1.r
    hdmaplna1.q
    hdmaplna1.v
    hdmaplna1.p
    @6
    lfladd
    syl112anc
end
