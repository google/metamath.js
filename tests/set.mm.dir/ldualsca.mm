include "csca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "clfn.mm"
include "cop.mm"
include "cplusg.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "ctp.mm"
include "cvsca.mm"
include "cv.mm"
include "csn.mm"
include "cmulr.mm"
include "co.mm"
include "cmpt2.mm"
include "cun.mm"
include "eqid.mm"
include "ldualset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "coppr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "lmodsca.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem ldualsca
  let wph: wff ph
  let cD: class D
  let cR: class R
  let cF: class F
  let cO: class O
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  assume ldualsca.f: |- F = ( Scalar ` W )
  assume ldualsca.o: |- O = ( oppR ` F )
  assume ldualsca.d: |- D = ( LDual ` W )
  assume ldualsca.r: |- R = ( Scalar ` D )
  assume ldualsca.w: |- ( ph -> W e. X )


  assert |- ( ph -> R = O )

  proof
    wph
    cD
    csca
    cfv
    cnx
    cbs
    cfv
    cW
    clfn
    cfv
    #
    cop
    cnx
    cplusg
    cfv
    cF
    cplusg
    cfv
    #
    cof
    @0
    @0
    cxp
    cres
    #
    cop
    cnx
    csca
    cfv
    cO
    cop
    ctp
    cnx
    cvsca
    cfv
    vk
    vf
    cF
    cbs
    cfv
    #
    @0
    vf
    cv
    cW
    cbs
    cfv
    #
    vk
    cv
    csn
    cxp
    cF
    cmulr
    cfv
    #
    cof
    co
    cmpt2
    #
    cop
    csn
    cun
    #
    csca
    cfv
    #
    cR
    cO
    wph
    cD
    @7
    csca
    wph
    cD
    @1
    @2
    cF
    @6
    @5
    vf
    vk
    @0
    @3
    cO
    @4
    cW
    cX
    @4
    eqid
    @1
    eqid
    @2
    eqid
    @0
    eqid
    ldualsca.d
    ldualsca.f
    @3
    eqid
    @5
    eqid
    ldualsca.o
    @6
    eqid
    ldualsca.w
    ldualset
    fveq2d
    ldualsca.r
    cO
    cvv
    wcel
    cO
    @8
    wceq
    cO
    cF
    coppr
    cfv
    cvv
    ldualsca.o
    cF
    coppr
    fvex
    eqeltri
    @0
    @2
    @6
    cO
    @7
    cvv
    @7
    eqid
    lmodsca
    ax-mp
    3eqtr4g
end
