include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "clmod.mm"
include "eqid.mm"
include "ldualvs.mm"
include "lflvscl.mm"
include "eqeltrd.mm"

theorem ldualvscl
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let cX: class X
  assume ldualvscl.f: |- F = ( LFnl ` W )
  assume ldualvscl.r: |- R = ( Scalar ` W )
  assume ldualvscl.k: |- K = ( Base ` R )
  assume ldualvscl.d: |- D = ( LDual ` W )
  assume ldualvscl.s: |- .x. = ( .s ` D )
  assume ldualvscl.w: |- ( ph -> W e. LMod )
  assume ldualvscl.x: |- ( ph -> X e. K )
  assume ldualvscl.g: |- ( ph -> G e. F )


  assert |- ( ph -> ( X .x. G ) e. F )

  proof
    wph
    cX
    cG
    c.x
    co
    cG
    cW
    cbs
    cfv
    #
    cX
    csn
    cxp
    cR
    cmulr
    cfv
    #
    cof
    co
    cF
    wph
    cD
    cR
    c.x
    @1
    cF
    cG
    cK
    @0
    cW
    cX
    clmod
    ldualvscl.f
    @0
    eqid
    #
    ldualvscl.r
    ldualvscl.k
    @1
    eqid
    #
    ldualvscl.d
    ldualvscl.s
    ldualvscl.w
    ldualvscl.x
    ldualvscl.g
    ldualvs
    wph
    cR
    cX
    @1
    cF
    cG
    cK
    @0
    cW
    @2
    ldualvscl.r
    ldualvscl.k
    @3
    ldualvscl.f
    ldualvscl.w
    ldualvscl.g
    ldualvscl.x
    lflvscl
    eqeltrd
end
