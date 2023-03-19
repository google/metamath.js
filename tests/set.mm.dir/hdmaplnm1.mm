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
include "lflmul.mm"
include "syl112anc.mm"

theorem hdmaplnm1
  let wph: wff ph
  let cA: class A
  let cB: class B
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
  assume hdmaplnm1.h: |- H = ( LHyp ` K )
  assume hdmaplnm1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmaplnm1.v: |- V = ( Base ` U )
  assume hdmaplnm1.t: |- .x. = ( .s ` U )
  assume hdmaplnm1.r: |- R = ( Scalar ` U )
  assume hdmaplnm1.b: |- B = ( Base ` R )
  assume hdmaplnm1.m: |- .X. = ( .r ` R )
  assume hdmaplnm1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaplnm1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmaplnm1.x: |- ( ph -> X e. V )
  assume hdmaplnm1.y: |- ( ph -> Y e. V )
  assume hdmaplnm1.a: |- ( ph -> A e. B )


  assert |- ( ph -> ( ( S ` Y ) ` ( A .x. X ) ) = ( A .X. ( ( S ` Y ) ` X ) ) )

  proof
    wph
    cU
    clmod
    wcel
    cY
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
    cA
    cX
    c.x
    co
    @0
    cfv
    cA
    cX
    @0
    cfv
    c.xp
    co
    wceq
    wph
    cU
    cH
    cK
    cW
    hdmaplnm1.h
    hdmaplnm1.u
    hdmaplnm1.k
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
    hdmaplnm1.h
    @2
    eqid
    #
    @3
    eqid
    #
    hdmaplnm1.u
    @1
    eqid
    #
    hdmaplnm1.k
    wph
    @2
    @3
    cS
    cY
    cU
    cH
    cK
    cV
    cW
    hdmaplnm1.h
    hdmaplnm1.u
    hdmaplnm1.v
    @4
    @5
    hdmaplnm1.s
    hdmaplnm1.k
    hdmaplnm1.y
    hdmapcl
    lcdvbaselfl
    hdmaplnm1.a
    hdmaplnm1.x
    cR
    cA
    c.x
    c.xp
    @1
    @0
    cB
    cV
    cU
    cX
    hdmaplnm1.r
    hdmaplnm1.b
    hdmaplnm1.m
    hdmaplnm1.v
    hdmaplnm1.t
    @6
    lflmul
    syl112anc
end
