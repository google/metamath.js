include "cbs.mm"
include "cfv.mm"
include "csca.mm"
include "cplusg.mm"
include "cltrn.mm"
include "cvsca.mm"
include "cmulr.mm"
include "ctendo.mm"
include "eqid.mm"
include "dvalveclem.mm"

theorem dvalvec
  let cU: class U
  let cH: class H
  let cK: class K
  let cW: class W
  let vf: setvar f
  let vt: setvar t
  let c.pd: class .+^
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vs: setvar s
  let cE: class E
  let vg: setvar g
  let c.pl: class .+
  let cT: class T
  let c.x: class .x.
  let c.xp: class .X.
  assume dvalvec.h: |- H = ( LHyp ` K )
  assume dvalvec.v: |- U = ( ( DVecA ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> U e. LVec )

  proof
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
    cK
    cW
    dvalvec.h
    dvalvec.v
    @4
    eqid
    @2
    eqid
    @7
    eqid
    @1
    eqid
    @0
    eqid
    @3
    eqid
    @6
    eqid
    @5
    eqid
    dvalveclem
end
