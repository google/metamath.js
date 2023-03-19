include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cfv.mm"
include "cdih.mm"
include "ccnv.mm"
include "coc.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "dih0rn.mm"
include "dochvalr.mm"
include "mpdan.mm"
include "cp1.mm"
include "cp0.mm"
include "dih0cnv.mm"
include "fveq2d.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "opoc0.mm"
include "syl.mm"
include "eqtrd.mm"
include "dih1.mm"

theorem doch0
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume doch0.h: |- H = ( LHyp ` K )
  assume doch0.u: |- U = ( ( DVecH ` K ) ` W )
  assume doch0.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume doch0.v: |- V = ( Base ` U )
  assume doch0.z: |- .0. = ( 0g ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> ( ._|_ ` { .0. } ) = V )

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
    c.0
    csn
    #
    c.pe
    cfv
    #
    @3
    cW
    cK
    cdih
    cfv
    cfv
    #
    ccnv
    cfv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    @5
    cfv
    #
    cV
    @2
    @3
    @5
    crn
    wcel
    @4
    @9
    wceq
    cU
    cH
    @5
    cK
    cW
    c.0
    doch0.h
    @5
    eqid
    #
    doch0.u
    doch0.z
    dih0rn
    cH
    @5
    cK
    c.pe
    @7
    cW
    @3
    @7
    eqid
    #
    doch0.h
    @10
    doch0.o
    dochvalr
    mpdan
    @2
    @9
    cK
    cp1
    cfv
    #
    @5
    cfv
    cV
    @2
    @8
    @12
    @5
    @2
    @8
    cK
    cp0
    cfv
    #
    @7
    cfv
    #
    @12
    @2
    @6
    @13
    @7
    cU
    cH
    @5
    cK
    cW
    @13
    c.0
    doch0.h
    @13
    eqid
    #
    @10
    doch0.u
    doch0.z
    dih0cnv
    fveq2d
    @2
    cK
    cops
    wcel
    #
    @14
    @12
    wceq
    @0
    @16
    @1
    cK
    hlop
    adantr
    @12
    cK
    @7
    @13
    @15
    @12
    eqid
    #
    @11
    opoc0
    syl
    eqtrd
    fveq2d
    cU
    @12
    cH
    @5
    cK
    cV
    cW
    @17
    doch0.h
    @10
    doch0.u
    doch0.v
    dih1
    eqtrd
    eqtrd
end
