include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cp0.mm"
include "cfv.mm"
include "csn.mm"
include "crn.mm"
include "eqid.mm"
include "dih0.mm"
include "cbs.mm"
include "wfn.mm"
include "dihfn.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "op0cl.mm"
include "syl.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem dih0rn
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let c.0: class .0.
  assume dih0rn.h: |- H = ( LHyp ` K )
  assume dih0rn.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih0rn.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih0rn.o: |- .0. = ( 0g ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> { .0. } e. ran I )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
    wa
    #
    cK
    cp0
    cfv
    #
    cI
    cfv
    #
    c.0
    csn
    cI
    crn
    #
    cU
    cH
    cI
    cK
    c.0
    cW
    @3
    @3
    eqid
    #
    dih0rn.h
    dih0rn.i
    dih0rn.u
    dih0rn.o
    dih0
    @2
    cI
    cK
    cbs
    cfv
    #
    wfn
    @3
    @7
    wcel
    #
    @4
    @5
    wcel
    @7
    cH
    cI
    cK
    cW
    @7
    eqid
    #
    dih0rn.h
    dih0rn.i
    dihfn
    @2
    cK
    cops
    wcel
    #
    @8
    @0
    @10
    @1
    cK
    hlop
    adantr
    @7
    cK
    @3
    @9
    @6
    op0cl
    syl
    @7
    @3
    cI
    fnfvelrn
    syl2anc
    eqeltrrd
end
