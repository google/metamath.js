include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "clvec.mm"
include "cbs.mm"
include "cfv.mm"
include "csca.mm"
include "cplusg.mm"
include "cltrn.mm"
include "cvsca.mm"
include "cmulr.mm"
include "ctendo.mm"
include "cminusg.mm"
include "c0g.mm"
include "eqid.mm"
include "dvhlveclem.mm"
include "syl.mm"

theorem dvhlvec
  let wph: wff ph
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  assume dvhlvec.h: |- H = ( LHyp ` K )
  assume dvhlvec.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvhlvec.k: |- ( ph -> ( K e. HL /\ W e. H ) )


  assert |- ( ph -> U e. LVec )

  proof
    wph
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cU
    clvec
    wcel
    dvhlvec.k
    cK
    cbs
    cfv
    #
    cU
    csca
    cfv
    #
    cU
    cplusg
    cfv
    #
    @1
    cplusg
    cfv
    #
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cU
    cvsca
    cfv
    #
    @1
    cmulr
    cfv
    #
    cU
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cH
    @1
    cminusg
    cfv
    #
    cK
    cW
    @1
    c0g
    cfv
    #
    @0
    eqid
    dvhlvec.h
    @4
    eqid
    @7
    eqid
    dvhlvec.u
    @1
    eqid
    @3
    eqid
    @2
    eqid
    @9
    eqid
    @8
    eqid
    @6
    eqid
    @5
    eqid
    dvhlveclem
    syl
end
