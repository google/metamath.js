include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cdih.mm"
include "ccnv.mm"
include "coc.mm"
include "cp0.mm"
include "csn.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "dih1rn.mm"
include "dochvalr.mm"
include "mpdan.mm"
include "cp1.mm"
include "dih1cnv.mm"
include "fveq2d.mm"
include "cops.mm"
include "hlop.mm"
include "adantr.mm"
include "opoc1.mm"
include "syl.mm"
include "eqtrd.mm"
include "dih0.mm"
include "3eqtrd.mm"

theorem doch1
  let cU: class U
  let cH: class H
  let cK: class K
  let c.pe: class ._|_
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume doch1.h: |- H = ( LHyp ` K )
  assume doch1.u: |- U = ( ( DVecH ` K ) ` W )
  assume doch1.o: |- ._|_ = ( ( ocH ` K ) ` W )
  assume doch1.v: |- V = ( Base ` U )
  assume doch1.z: |- .0. = ( 0g ` U )


  assert |- ( ( K e. HL /\ W e. H ) -> ( ._|_ ` V ) = { .0. } )

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
    cV
    c.pe
    cfv
    #
    cV
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
    @4
    cfv
    #
    cK
    cp0
    cfv
    #
    @4
    cfv
    c.0
    csn
    @2
    cV
    @4
    crn
    wcel
    @3
    @8
    wceq
    cU
    cH
    @4
    cK
    cV
    cW
    doch1.h
    @4
    eqid
    #
    doch1.u
    doch1.v
    dih1rn
    cH
    @4
    cK
    c.pe
    @6
    cW
    cV
    @6
    eqid
    #
    doch1.h
    @10
    doch1.o
    dochvalr
    mpdan
    @2
    @7
    @9
    @4
    @2
    @7
    cK
    cp1
    cfv
    #
    @6
    cfv
    #
    @9
    @2
    @5
    @12
    @6
    cU
    @12
    cH
    @4
    cK
    cV
    cW
    doch1.h
    @12
    eqid
    #
    @10
    doch1.u
    doch1.v
    dih1cnv
    fveq2d
    @2
    cK
    cops
    wcel
    #
    @13
    @9
    wceq
    @0
    @15
    @1
    cK
    hlop
    adantr
    @12
    cK
    @6
    @9
    @9
    eqid
    #
    @14
    @11
    opoc1
    syl
    eqtrd
    fveq2d
    cU
    cH
    @4
    cK
    c.0
    cW
    @9
    @16
    doch1.h
    @10
    doch1.u
    doch1.z
    dih0
    3eqtrd
end
