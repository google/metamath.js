include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cof.mm"
include "eqid.mm"
include "lflvsass.mm"
include "clmod.mm"
include "crg.mm"
include "wcel.mm"
include "lmodring.mm"
include "syl.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "ldualvs.mm"
include "lflvscl.mm"
include "3eqtr4d.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem ldualvsass
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  assume ldualvsass.f: |- F = ( LFnl ` W )
  assume ldualvsass.r: |- R = ( Scalar ` W )
  assume ldualvsass.k: |- K = ( Base ` R )
  assume ldualvsass.t: |- .X. = ( .r ` R )
  assume ldualvsass.d: |- D = ( LDual ` W )
  assume ldualvsass.s: |- .x. = ( .s ` D )
  assume ldualvsass.w: |- ( ph -> W e. LMod )
  assume ldualvsass.x: |- ( ph -> X e. K )
  assume ldualvsass.y: |- ( ph -> Y e. K )
  assume ldualvsass.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( ( Y .X. X ) .x. G ) = ( X .x. ( Y .x. G ) ) )

  proof
    wph
    cY
    cX
    c.xp
    co
    #
    cG
    c.x
    co
    #
    cX
    cG
    cW
    cbs
    cfv
    #
    cY
    csn
    cxp
    c.xp
    cof
    #
    co
    #
    c.x
    co
    #
    cX
    cY
    cG
    c.x
    co
    #
    c.x
    co
    wph
    cG
    @2
    @0
    csn
    cxp
    @3
    co
    @4
    @2
    cX
    csn
    cxp
    @3
    co
    @1
    @5
    wph
    cR
    c.xp
    cF
    cG
    cK
    @2
    cW
    cY
    cX
    @2
    eqid
    #
    ldualvsass.r
    ldualvsass.k
    ldualvsass.t
    ldualvsass.f
    ldualvsass.w
    ldualvsass.y
    ldualvsass.x
    ldualvsass.g
    lflvsass
    wph
    cD
    cR
    c.x
    c.xp
    cF
    cG
    cK
    @2
    cW
    @0
    clmod
    ldualvsass.f
    @7
    ldualvsass.r
    ldualvsass.k
    ldualvsass.t
    ldualvsass.d
    ldualvsass.s
    ldualvsass.w
    wph
    cR
    crg
    wcel
    #
    cY
    cK
    wcel
    cX
    cK
    wcel
    @0
    cK
    wcel
    wph
    cW
    clmod
    wcel
    @8
    ldualvsass.w
    cR
    cW
    ldualvsass.r
    lmodring
    syl
    ldualvsass.y
    ldualvsass.x
    cK
    cR
    c.xp
    cY
    cX
    ldualvsass.k
    ldualvsass.t
    ringcl
    syl3anc
    ldualvsass.g
    ldualvs
    wph
    cD
    cR
    c.x
    c.xp
    cF
    @4
    cK
    @2
    cW
    cX
    clmod
    ldualvsass.f
    @7
    ldualvsass.r
    ldualvsass.k
    ldualvsass.t
    ldualvsass.d
    ldualvsass.s
    ldualvsass.w
    ldualvsass.x
    wph
    cR
    cY
    c.xp
    cF
    cG
    cK
    @2
    cW
    @7
    ldualvsass.r
    ldualvsass.k
    ldualvsass.t
    ldualvsass.f
    ldualvsass.w
    ldualvsass.g
    ldualvsass.y
    lflvscl
    ldualvs
    3eqtr4d
    wph
    @6
    @4
    cX
    c.x
    wph
    cD
    cR
    c.x
    c.xp
    cF
    cG
    cK
    @2
    cW
    cY
    clmod
    ldualvsass.f
    @7
    ldualvsass.r
    ldualvsass.k
    ldualvsass.t
    ldualvsass.d
    ldualvsass.s
    ldualvsass.w
    ldualvsass.y
    ldualvsass.g
    ldualvs
    oveq2d
    eqtr4d
end
