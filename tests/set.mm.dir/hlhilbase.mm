include "cbs.mm"
include "cfv.mm"
include "cnx.mm"
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
include "phlbase.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem hlhilbase
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hlhilbase.h: |- H = ( LHyp ` K )
  assume hlhilbase.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilbase.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilbase.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilbase.m: |- M = ( Base ` L )


  assert |- ( ph -> M = ( Base ` U ) )

  proof
    wph
    cU
    cbs
    cfv
    cnx
    cbs
    cfv
    cM
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
    vx
    vy
    cM
    cM
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
    cbs
    cfv
    #
    cM
    wph
    cU
    @7
    cbs
    wph
    vx
    vy
    @0
    @3
    @5
    @4
    cL
    @1
    @2
    cH
    @6
    cK
    cU
    cM
    cW
    hlhilbase.h
    hlhilbase.u
    hlhilbase.l
    hlhilbase.m
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
    @5
    eqid
    @6
    eqid
    hlhilbase.k
    hlhilset
    fveq2d
    cM
    cvv
    wcel
    cM
    @8
    wceq
    cM
    cL
    cbs
    cfv
    cvv
    hlhilbase.m
    cL
    cbs
    fvex
    eqeltri
    cM
    @0
    @3
    @4
    @7
    @6
    cvv
    @7
    eqid
    phlbase
    ax-mp
    syl6reqr
end
