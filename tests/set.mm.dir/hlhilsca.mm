include "csca.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cdvh.mm"
include "cop.mm"
include "cplusg.mm"
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
include "cstv.mm"
include "csts.mm"
include "co.mm"
include "ovex.mm"
include "eqeltri.mm"
include "phlsca.mm"
include "ax-mp.mm"
include "syl6reqr.mm"

theorem hlhilsca
  let wph: wff ph
  let cR: class R
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let cK: class K
  let cW: class W
  let vx: setvar x
  let vy: setvar y
  assume hlhilbase.h: |- H = ( LHyp ` K )
  assume hlhilbase.u: |- U = ( ( HLHil ` K ) ` W )
  assume hlhilbase.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hlhilsca.e: |- E = ( ( EDRing ` K ) ` W )
  assume hlhilsca.g: |- G = ( ( HGMap ` K ) ` W )
  assume hlhilsca.r: |- R = ( E sSet <. ( *r ` ndx ) , G >. )


  assert |- ( ph -> R = ( Scalar ` U ) )

  proof
    wph
    cU
    csca
    cfv
    cnx
    cbs
    cfv
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cbs
    cfv
    #
    cop
    cnx
    cplusg
    cfv
    @0
    cplusg
    cfv
    #
    cop
    cnx
    csca
    cfv
    cR
    cop
    ctp
    cnx
    cvsca
    cfv
    @0
    cvsca
    cfv
    #
    cop
    cnx
    cip
    cfv
    vx
    vy
    @1
    @1
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
    csca
    cfv
    #
    cR
    wph
    cU
    @6
    csca
    wph
    vx
    vy
    @2
    cR
    @4
    @3
    @0
    cE
    cG
    cH
    @5
    cK
    cU
    @1
    cW
    hlhilbase.h
    hlhilbase.u
    @0
    eqid
    @1
    eqid
    @2
    eqid
    hlhilsca.e
    hlhilsca.g
    hlhilsca.r
    @3
    eqid
    @4
    eqid
    @5
    eqid
    hlhilbase.k
    hlhilset
    fveq2d
    cR
    cvv
    wcel
    cR
    @7
    wceq
    cR
    cE
    cnx
    cstv
    cfv
    cG
    cop
    #
    csts
    co
    cvv
    hlhilsca.r
    cE
    @8
    csts
    ovex
    eqeltri
    @1
    @2
    cR
    @3
    @6
    @5
    cvv
    @6
    eqid
    phlsca
    ax-mp
    syl6reqr
end
