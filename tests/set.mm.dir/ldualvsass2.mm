include "co.mm"
include "cmulr.mm"
include "cfv.mm"
include "clmod.mm"
include "eqid.mm"
include "ldualsmul.mm"
include "oveq1d.mm"
include "ldualvsass.mm"
include "eqtrd.mm"

theorem ldualvsass2
  let wph: wff ph
  let cD: class D
  let cQ: class Q
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ldualvsass2.f: |- F = ( LFnl ` W )
  assume ldualvsass2.r: |- R = ( Scalar ` W )
  assume ldualvsass2.k: |- K = ( Base ` R )
  assume ldualvsass2.d: |- D = ( LDual ` W )
  assume ldualvsass2.q: |- Q = ( Scalar ` D )
  assume ldualvsass2.t: |- .X. = ( .r ` Q )
  assume ldualvsass2.s: |- .x. = ( .s ` D )
  assume ldualvsass2.w: |- ( ph -> W e. LMod )
  assume ldualvsass2.x: |- ( ph -> X e. K )
  assume ldualvsass2.y: |- ( ph -> Y e. K )
  assume ldualvsass2.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( X .X. Y ) .x. G ) = ( X .x. ( Y .x. G ) ) )

  proof
    wph
    cX
    cY
    c.xp
    co
    #
    cG
    c.x
    co
    cY
    cX
    cR
    cmulr
    cfv
    #
    co
    #
    cG
    c.x
    co
    cX
    cY
    cG
    c.x
    co
    c.x
    co
    wph
    @0
    @2
    cG
    c.x
    wph
    cD
    cQ
    c.xp
    @1
    cR
    cK
    clmod
    cW
    cX
    cY
    ldualvsass2.r
    ldualvsass2.k
    @1
    eqid
    #
    ldualvsass2.d
    ldualvsass2.q
    ldualvsass2.t
    ldualvsass2.w
    ldualvsass2.x
    ldualvsass2.y
    ldualsmul
    oveq1d
    wph
    cD
    cR
    c.x
    @1
    cF
    cG
    cK
    cW
    cX
    cY
    ldualvsass2.f
    ldualvsass2.r
    ldualvsass2.k
    @3
    ldualvsass2.d
    ldualvsass2.s
    ldualvsass2.w
    ldualvsass2.x
    ldualvsass2.y
    ldualvsass2.g
    ldualvsass
    eqtrd
end
