include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cp1.mm"
include "cfv.mm"
include "crn.mm"
include "eqid.mm"
include "dih1.mm"
include "cbs.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "op1cl.mm"
include "syl.mm"
include "dihcl.mm"
include "mpdan.mm"
include "eqeltrrd.mm"

theorem dih1rn
  let cU: class U
  let cH: class H
  let cI: class I
  let cK: class K
  let cV: class V
  let cW: class W
  assume dih1rn.h: |- H = ( LHyp ` K )
  assume dih1rn.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dih1rn.u: |- U = ( ( DVecH ` K ) ` W )
  assume dih1rn.v: |- V = ( Base ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> V e. ran I )

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
    cp1
    cfv
    #
    cI
    cfv
    #
    cV
    cI
    crn
    #
    cU
    @3
    cH
    cI
    cK
    cV
    cW
    @3
    eqid
    #
    dih1rn.h
    dih1rn.i
    dih1rn.u
    dih1rn.v
    dih1
    @2
    @3
    cK
    cbs
    cfv
    #
    wcel
    #
    @4
    @5
    wcel
    @2
    cK
    cops
    wcel
    #
    @8
    @0
    @9
    @1
    cK
    hlop
    adantr
    @7
    @3
    cK
    @7
    eqid
    #
    @6
    op1cl
    syl
    @7
    cH
    cI
    cK
    cW
    @3
    @10
    dih1rn.h
    dih1rn.i
    dihcl
    mpdan
    eqeltrrd
end
