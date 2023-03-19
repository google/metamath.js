include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
include "cop.mm"
include "cplusg.mm"
include "csca.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "coppr.mm"
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
include "clfn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "lmodbase.mm"
include "ax-mp.mm"
include "3eqtr4g.mm"

theorem ldualvbase
  let wph: wff ph
  let cD: class D
  let cF: class F
  let cV: class V
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  assume ldualvbase.f: |- F = ( LFnl ` W )
  assume ldualvbase.d: |- D = ( LDual ` W )
  assume ldualvbase.v: |- V = ( Base ` D )
  assume ldualvbase.w: |- ( ph -> W e. X )


  assert |- ( ph -> V = F )

  proof
    wph
    cD
    cbs
    cfv
    cnx
    cbs
    cfv
    cF
    cop
    cnx
    cplusg
    cfv
    cW
    csca
    cfv
    #
    cplusg
    cfv
    #
    cof
    cF
    cF
    cxp
    cres
    #
    cop
    cnx
    csca
    cfv
    @0
    coppr
    cfv
    #
    cop
    ctp
    cnx
    cvsca
    cfv
    vk
    vf
    @0
    cbs
    cfv
    #
    cF
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
    @0
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
    cbs
    cfv
    #
    cV
    cF
    wph
    cD
    @8
    cbs
    wph
    cD
    @1
    @2
    @0
    @7
    @6
    vf
    vk
    cF
    @4
    @3
    @5
    cW
    cX
    @5
    eqid
    @1
    eqid
    @2
    eqid
    ldualvbase.f
    ldualvbase.d
    @0
    eqid
    @4
    eqid
    @6
    eqid
    @3
    eqid
    @7
    eqid
    ldualvbase.w
    ldualset
    fveq2d
    ldualvbase.v
    cF
    cvv
    wcel
    cF
    @9
    wceq
    cF
    cW
    clfn
    cfv
    cvv
    ldualvbase.f
    cW
    clfn
    fvex
    eqeltri
    cF
    @2
    @7
    @3
    @8
    cvv
    @8
    eqid
    lmodbase
    ax-mp
    3eqtr4g
end
