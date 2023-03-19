include "cvsca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "csca.mm"
include "coppr.mm"
include "ctp.mm"
include "cv.mm"
include "csn.mm"
include "co.mm"
include "cmpt2.mm"
include "cun.mm"
include "eqid.mm"
include "ldualset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "clfn.mm"
include "mpt2ex.mm"
include "lmodvsca.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "3eqtr4g.mm"

theorem ldualfvs
  let wph: wff ph
  let cD: class D
  let cR: class R
  let c.xb: class .xb
  let c.x: class .x.
  let c.xp: class .X.
  let vf: setvar f
  let vk: setvar k
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let cY: class Y
  let cG: class G
  let cX: class X
  assume ldualfvs.f: |- F = ( LFnl ` W )
  assume ldualfvs.v: |- V = ( Base ` W )
  assume ldualfvs.r: |- R = ( Scalar ` W )
  assume ldualfvs.k: |- K = ( Base ` R )
  assume ldualfvs.t: |- .X. = ( .r ` R )
  assume ldualfvs.d: |- D = ( LDual ` W )
  assume ldualfvs.s: |- .xb = ( .s ` D )
  assume ldualfvs.w: |- ( ph -> W e. Y )
  assume ldualfvs.m: |- .x. = ( k e. K , f e. F |-> ( f oF .X. ( V X. { k } ) ) )

  disjoint f k
  disjoint F f
  disjoint F k
  disjoint K f
  disjoint K k
  disjoint .X. f
  disjoint .X. k
  disjoint V f
  disjoint V k
  disjoint W f
  disjoint W k
  disjoint G f
  disjoint G k
  disjoint X f
  disjoint X k
  assert |- ( ph -> .xb = .x. )

  proof
    wph
    cD
    cvsca
    cfv
    cnx
    cbs
    cfv
    cF
    cop
    cnx
    cplusg
    cfv
    cR
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
    cK
    cF
    vf
    cv
    cV
    vk
    cv
    csn
    cxp
    c.xp
    cof
    co
    #
    cmpt2
    #
    cop
    csn
    cun
    #
    cvsca
    cfv
    #
    c.xb
    c.x
    wph
    cD
    @5
    cvsca
    wph
    cD
    @0
    @1
    cR
    @4
    c.xp
    vf
    vk
    cF
    cK
    @2
    cV
    cW
    cY
    ldualfvs.v
    @0
    eqid
    @1
    eqid
    ldualfvs.f
    ldualfvs.d
    ldualfvs.r
    ldualfvs.k
    ldualfvs.t
    @2
    eqid
    @4
    eqid
    ldualfvs.w
    ldualset
    fveq2d
    ldualfvs.s
    c.x
    @4
    @6
    ldualfvs.m
    @4
    cvv
    wcel
    @4
    @6
    wceq
    vk
    vf
    cK
    cF
    @3
    cK
    cR
    cbs
    cfv
    cvv
    ldualfvs.k
    cR
    cbs
    fvex
    eqeltri
    cF
    cW
    clfn
    cfv
    cvv
    ldualfvs.f
    cW
    clfn
    fvex
    eqeltri
    mpt2ex
    cF
    @1
    @4
    @2
    @5
    cvv
    @5
    eqid
    lmodvsca
    ax-mp
    eqtri
    3eqtr4g
end
