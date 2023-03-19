include "cplusg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "csca.mm"
include "coppr.mm"
include "ctp.mm"
include "cvsca.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmulr.mm"
include "cof.mm"
include "co.mm"
include "cmpt2.mm"
include "cun.mm"
include "eqid.mm"
include "ldualset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cres.mm"
include "clfn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "id.mm"
include "ofmresex.mm"
include "ax-mp.mm"
include "lmodplusg.mm"
include "3eqtr4g.mm"

theorem ldualfvadd
  let wph: wff ph
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let c.pb: class .+b
  let cR: class R
  let cF: class F
  let cW: class W
  let cX: class X
  let vf: setvar f
  let vk: setvar k
  assume ldualvadd.f: |- F = ( LFnl ` W )
  assume ldualvadd.r: |- R = ( Scalar ` W )
  assume ldualvadd.a: |- .+ = ( +g ` R )
  assume ldualvadd.d: |- D = ( LDual ` W )
  assume ldualvadd.p: |- .+b = ( +g ` D )
  assume ldualvadd.w: |- ( ph -> W e. X )
  assume ldualfvadd.q: |- .+^ = ( oF .+ |` ( F X. F ) )


  assert |- ( ph -> .+b = .+^ )

  proof
    wph
    cD
    cplusg
    cfv
    cnx
    cbs
    cfv
    cF
    cop
    cnx
    cplusg
    cfv
    c.pd
    cop
    cnx
    csca
    cfv
    cR
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
    cR
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
    cR
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
    cplusg
    cfv
    #
    c.pb
    c.pd
    wph
    cD
    @5
    cplusg
    wph
    cD
    c.pl
    c.pd
    cR
    @4
    @3
    vf
    vk
    cF
    @1
    @0
    @2
    cW
    cX
    @2
    eqid
    ldualvadd.a
    ldualfvadd.q
    ldualvadd.f
    ldualvadd.d
    ldualvadd.r
    @1
    eqid
    @3
    eqid
    @0
    eqid
    @4
    eqid
    ldualvadd.w
    ldualset
    fveq2d
    ldualvadd.p
    c.pd
    cvv
    wcel
    c.pd
    @6
    wceq
    c.pd
    c.pl
    cof
    cF
    cF
    cxp
    cres
    #
    cvv
    ldualfvadd.q
    cF
    cvv
    wcel
    #
    @7
    cvv
    wcel
    cF
    cW
    clfn
    cfv
    cvv
    ldualvadd.f
    cW
    clfn
    fvex
    eqeltri
    @8
    cF
    cF
    c.pl
    cvv
    cvv
    @8
    id
    #
    @9
    ofmresex
    ax-mp
    eqeltri
    cF
    c.pd
    @4
    @0
    @5
    cvv
    @5
    eqid
    lmodplusg
    ax-mp
    3eqtr4g
end
