include "cip.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "csca.mm"
include "cedring.mm"
include "cstv.mm"
include "chg.mm"
include "csts.mm"
include "co.mm"
include "ctp.mm"
include "cvsca.mm"
include "cpr.mm"
include "cun.mm"
include "eqid.mm"
include "hlhilset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cmpt2.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "phlip.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem hlhilip
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cU: class U
  let cH: class H
  let c.xi: class .,
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume hlhilip.h: |- H = ( LHyp ` K )
  assume hlhilip.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilip.v: |- V = ( Base ` L )
  assume hlhilip.s: |- S = ( ( HDMap ` K ) ` W )
  assume hlhilip.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilip.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilip.p: |- ., = ( x e. V , y e. V |-> ( ( S ` y ) ` x ) )

  disjoint x y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint V x
  disjoint V y
  disjoint W x
  disjoint W y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ., = ( .i ` U ) )

  proof
    wph
    cU
    cip
    cfv
    cnx
    cbs
    cfv
    cV
    cop
    cnx
    cplusg
    cfv
    cL
    cplusg
    cfv
    #
    cop
    cnx
    csca
    cfv
    cW
    cK
    cedring
    cfv
    cfv
    #
    cnx
    cstv
    cfv
    cW
    cK
    chg
    cfv
    cfv
    #
    cop
    csts
    co
    #
    cop
    ctp
    cnx
    cvsca
    cfv
    cL
    cvsca
    cfv
    #
    cop
    cnx
    cip
    cfv
    c.xi
    cop
    cpr
    cun
    #
    cip
    cfv
    #
    c.xi
    wph
    cU
    @5
    cip
    wph
    vx
    vy
    @0
    @3
    cS
    @4
    cL
    @1
    @2
    cH
    c.xi
    cK
    cU
    cV
    cW
    hlhilip.h
    hlhilip.u
    hlhilip.l
    hlhilip.v
    @0
    eqid
    @1
    eqid
    @2
    eqid
    @3
    eqid
    @4
    eqid
    hlhilip.s
    hlhilip.p
    hlhilip.k
    hlhilset
    fveq2d
    c.xi
    cvv
    wcel
    c.xi
    @6
    wceq
    c.xi
    vx
    vy
    cV
    cV
    vx
    cv
    vy
    cv
    cS
    cfv
    cfv
    #
    cmpt2
    cvv
    hlhilip.p
    vx
    vy
    cV
    cV
    @7
    cV
    cL
    cbs
    cfv
    cvv
    hlhilip.v
    cL
    cbs
    fvex
    eqeltri
    #
    @8
    mpt2ex
    eqeltri
    cV
    @0
    @3
    @4
    @5
    c.xi
    cvv
    @5
    eqid
    phlip
    ax-mp
    syl6reqr
end
