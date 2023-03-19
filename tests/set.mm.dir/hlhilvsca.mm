include "cvsca.mm"
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
include "cip.mm"
include "cv.mm"
include "chdma.mm"
include "cmpt2.mm"
include "cpr.mm"
include "cun.mm"
include "eqid.mm"
include "hlhilset.mm"
include "fveq2d.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "fvex.mm"
include "eqeltri.mm"
include "phlvsca.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem hlhilvsca
  let wph: wff ph
  let c.x: class .x.
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hlhilvsca.h: |- H = ( LHyp ` K )
  assume hlhilvsca.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilvsca.t: |- .x. = ( .s ` L )
  assume hlhilvsca.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilvsca.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> .x. = ( .s ` U ) )

  proof
    wph
    cU
    cvsca
    cfv
    cnx
    cbs
    cfv
    cL
    cbs
    cfv
    #
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
    c.x
    cop
    cnx
    cip
    cfv
    vx
    vy
    @0
    @0
    vx
    cv
    vy
    cv
    cW
    cK
    chdma
    cfv
    cfv
    #
    cfv
    cfv
    cmpt2
    #
    cop
    cpr
    cun
    #
    cvsca
    cfv
    #
    c.x
    wph
    cU
    @7
    cvsca
    wph
    vx
    vy
    @1
    @4
    @5
    c.x
    cL
    @2
    @3
    cH
    @6
    cK
    cU
    @0
    cW
    hlhilvsca.h
    hlhilvsca.u
    hlhilvsca.l
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
    hlhilvsca.t
    @5
    eqid
    @6
    eqid
    hlhilvsca.k
    hlhilset
    fveq2d
    c.x
    cvv
    wcel
    c.x
    @8
    wceq
    c.x
    cL
    cvsca
    cfv
    cvv
    hlhilvsca.t
    cL
    cvsca
    fvex
    eqeltri
    @0
    @1
    @4
    c.x
    @7
    @6
    cvv
    @7
    eqid
    phlvsca
    ax-mp
    syl6reqr
end
