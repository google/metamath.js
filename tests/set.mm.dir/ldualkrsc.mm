include "co.mm"
include "cfv.mm"
include "cbs.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "clvec.mm"
include "eqid.mm"
include "ldualvs.mm"
include "fveq2d.mm"
include "lkrsc.mm"
include "eqtrd.mm"

theorem ldualkrsc
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
  let c.0: class .0.
  assume ldualkrsc.r: |- R = ( Scalar ` W )
  assume ldualkrsc.k: |- K = ( Base ` R )
  assume ldualkrsc.o: |- .0. = ( 0g ` R )
  assume ldualkrsc.f: |- F = ( LFnl ` W )
  assume ldualkrsc.l: |- L = ( LKer ` W )
  assume ldualkrsc.d: |- D = ( LDual ` W )
  assume ldualkrsc.s: |- .x. = ( .s ` D )
  assume ldualkrsc.w: |- ( ph -> W e. LVec )
  assume ldualkrsc.g: |- ( ph -> G e. F )
  assume ldualkrsc.x: |- ( ph -> X e. K )
  assume ldualkrsc.e: |- ( ph -> X =/= .0. )


  assert |- ( ph -> ( L ` ( X .x. G ) ) = ( L ` G ) )

  proof
    wph
    cX
    cG
    c.x
    co
    #
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
    cG
    cL
    cfv
    wph
    @0
    @3
    cL
    wph
    cD
    cR
    c.x
    @2
    cF
    cG
    cK
    @1
    cW
    cX
    clvec
    ldualkrsc.f
    @1
    eqid
    #
    ldualkrsc.r
    ldualkrsc.k
    @2
    eqid
    #
    ldualkrsc.d
    ldualkrsc.s
    ldualkrsc.w
    ldualkrsc.x
    ldualkrsc.g
    ldualvs
    fveq2d
    wph
    cR
    cX
    @2
    cF
    cG
    cK
    cL
    @1
    cW
    c.0
    @4
    ldualkrsc.r
    ldualkrsc.k
    @5
    ldualkrsc.f
    ldualkrsc.l
    ldualkrsc.w
    ldualkrsc.g
    ldualkrsc.x
    ldualkrsc.o
    ldualkrsc.e
    lkrsc
    eqtrd
end
