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
include "lflsub.mm"
include "syl112anc.mm"

theorem hdmaplns1
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cU: class U
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume hdmaplns1.h: |- H = ( LHyp ` K )
  assume hdmaplns1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmaplns1.v: |- V = ( Base ` U )
  assume hdmaplns1.m: |- .- = ( -g ` U )
  assume hdmaplns1.r: |- R = ( Scalar ` U )
  assume hdmaplns1.n: |- N = ( -g ` R )
  assume hdmaplns1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmaplns1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmaplns1.x: |- ( ph -> X e. V )
  assume hdmaplns1.y: |- ( ph -> Y e. V )
  assume hdmaplns1.z: |- ( ph -> Z e. V )


  assert |- ( ph -> ( ( S ` Z ) ` ( X .- Y ) ) = ( ( ( S ` Z ) ` X ) N ( ( S ` Z ) ` Y ) ) )

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
    c.mi
    co
    @0
    cfv
    cX
    @0
    cfv
    cY
    @0
    cfv
    cN
    co
    wceq
    wph
    cU
    cH
    cK
    cW
    hdmaplns1.h
    hdmaplns1.u
    hdmaplns1.k
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
    hdmaplns1.h
    @2
    eqid
    #
    @3
    eqid
    #
    hdmaplns1.u
    @1
    eqid
    #
    hdmaplns1.k
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
    hdmaplns1.h
    hdmaplns1.u
    hdmaplns1.v
    @4
    @5
    hdmaplns1.s
    hdmaplns1.k
    hdmaplns1.z
    hdmapcl
    lcdvbaselfl
    hdmaplns1.x
    hdmaplns1.y
    cR
    @1
    @0
    cN
    c.mi
    cV
    cU
    cX
    cY
    hdmaplns1.r
    hdmaplns1.n
    hdmaplns1.v
    hdmaplns1.m
    @6
    lflsub
    syl112anc
end
