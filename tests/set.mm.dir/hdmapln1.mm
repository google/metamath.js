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
include "lfli.mm"
include "syl113anc.mm"

theorem hdmapln1
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
  let cH: class H
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume hdmapln1.h: |- H = ( LHyp ` K )
  assume hdmapln1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapln1.v: |- V = ( Base ` U )
  assume hdmapln1.p: |- .+ = ( +g ` U )
  assume hdmapln1.t: |- .x. = ( .s ` U )
  assume hdmapln1.r: |- R = ( Scalar ` U )
  assume hdmapln1.b: |- B = ( Base ` R )
  assume hdmapln1.q: |- .+^ = ( +g ` R )
  assume hdmapln1.m: |- .X. = ( .r ` R )
  assume hdmapln1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapln1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapln1.x: |- ( ph -> X e. V )
  assume hdmapln1.y: |- ( ph -> Y e. V )
  assume hdmapln1.z: |- ( ph -> Z e. V )
  assume hdmapln1.a: |- ( ph -> A e. B )


  assert |- ( ph -> ( ( S ` Z ) ` ( ( A .x. X ) .+ Y ) ) = ( ( A .X. ( ( S ` Z ) ` X ) ) .+^ ( ( S ` Z ) ` Y ) ) )

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
    cA
    cB
    wcel
    cX
    cV
    wcel
    cY
    cV
    wcel
    cA
    cX
    c.x
    co
    cY
    c.pl
    co
    @0
    cfv
    cA
    cX
    @0
    cfv
    c.xp
    co
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
    hdmapln1.h
    hdmapln1.u
    hdmapln1.k
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
    hdmapln1.h
    @2
    eqid
    #
    @3
    eqid
    #
    hdmapln1.u
    @1
    eqid
    #
    hdmapln1.k
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
    hdmapln1.h
    hdmapln1.u
    hdmapln1.v
    @4
    @5
    hdmapln1.s
    hdmapln1.k
    hdmapln1.z
    hdmapcl
    lcdvbaselfl
    hdmapln1.a
    hdmapln1.x
    hdmapln1.y
    cR
    c.pl
    c.pd
    cA
    c.x
    c.xp
    @1
    @0
    cB
    cV
    cU
    cX
    cY
    clmod
    hdmapln1.v
    hdmapln1.p
    hdmapln1.r
    hdmapln1.t
    hdmapln1.b
    hdmapln1.q
    hdmapln1.m
    @6
    lfli
    syl113anc
end
