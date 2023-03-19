include "cfv.mm"
include "cbs.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "co.mm"
include "eqid.mm"
include "lkrscss.mm"
include "clvec.mm"
include "ldualvs.mm"
include "fveq2d.mm"
include "sseqtr4d.mm"

theorem lkrss
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cK: class K
  let cL: class L
  let cW: class W
  let cX: class X
  assume lkrss.r: |- R = ( Scalar ` W )
  assume lkrss.k: |- K = ( Base ` R )
  assume lkrss.f: |- F = ( LFnl ` W )
  assume lkrss.l: |- L = ( LKer ` W )
  assume lkrss.d: |- D = ( LDual ` W )
  assume lkrss.s: |- .x. = ( .s ` D )
  assume lkrss.w: |- ( ph -> W e. LVec )
  assume lkrss.g: |- ( ph -> G e. F )
  assume lkrss.x: |- ( ph -> X e. K )


  assert |- ( ph -> ( L ` G ) C_ ( L ` ( X .x. G ) ) )

  proof
    wph
    cG
    cL
    cfv
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
    #
    cL
    cfv
    cX
    cG
    c.x
    co
    #
    cL
    cfv
    wph
    cR
    cX
    @1
    cF
    cG
    cK
    cL
    @0
    cW
    @0
    eqid
    #
    lkrss.r
    lkrss.k
    @1
    eqid
    #
    lkrss.f
    lkrss.l
    lkrss.w
    lkrss.g
    lkrss.x
    lkrscss
    wph
    @3
    @2
    cL
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
    clvec
    lkrss.f
    @4
    lkrss.r
    lkrss.k
    @5
    lkrss.d
    lkrss.s
    lkrss.w
    lkrss.x
    lkrss.g
    ldualvs
    fveq2d
    sseqtr4d
end
