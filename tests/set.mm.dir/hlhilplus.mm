include "cplusg.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
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
include "phlplusg.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem hlhilplus
  let wph: wff ph
  let c.pl: class .+
  let cU: class U
  let cH: class H
  let cK: class K
  let cL: class L
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hlhilbase.h: |- H = ( LHyp ` K )
  assume hlhilbase.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilbase.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilbase.l: |- L = ( ( DVecH ` K ) ` W )
  assume hlhilplus.a: |- .+ = ( +g ` L )


  assert |- ( ph -> .+ = ( +g ` U ) )

  proof
    wph
    cU
    cplusg
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
    c.pl
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
    cplusg
    cfv
    #
    c.pl
    wph
    cU
    @7
    cplusg
    wph
    vx
    vy
    c.pl
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
    @0
    cW
    hlhilbase.h
    hlhilbase.u
    hlhilbase.l
    @0
    eqid
    hlhilplus.a
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
    c.pl
    cvv
    wcel
    c.pl
    @8
    wceq
    c.pl
    cL
    cplusg
    cfv
    cvv
    hlhilplus.a
    cL
    cplusg
    fvex
    eqeltri
    @0
    c.pl
    @3
    @4
    @7
    @6
    cvv
    @7
    eqid
    phlplusg
    ax-mp
    syl6reqr
end
