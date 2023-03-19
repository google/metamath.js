include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "crn.mm"
include "cfv.mm"
include "ccnv.mm"
include "coc.mm"
include "eqid.mm"
include "dochvalr.mm"
include "fveq2d.mm"
include "wceq.mm"
include "cbs.mm"
include "cops.mm"
include "hlop.mm"
include "ad2antrr.mm"
include "dihcnvcl.mm"
include "opoccl.mm"
include "syl2anc.mm"
include "dihcl.mm"
include "syldan.mm"
include "dihcnvid1.mm"
include "opococ.mm"
include "eqtrd.mm"
include "dihcnvid2.mm"

theorem dochoc
  let cH: class H
  let cI: class I
  let cK: class K
  let c.pe: class ._|_
  let cW: class W
  let cX: class X
  assume dochoc.h: |- H = ( LHyp ` K )
  assume dochoc.i: |- I = ( ( DIsoH ` K ) ` W )
  assume dochoc.o: |- ._|_ = ( ( ocH ` K ) ` W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ X e. ran I ) -> ( ._|_ ` ( ._|_ ` X ) ) = X )

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
    cX
    cI
    crn
    #
    wcel
    #
    wa
    #
    cX
    c.pe
    cfv
    #
    c.pe
    cfv
    cX
    cI
    ccnv
    #
    cfv
    #
    cK
    coc
    cfv
    #
    cfv
    #
    cI
    cfv
    #
    c.pe
    cfv
    #
    cX
    @5
    @6
    @11
    c.pe
    cH
    cI
    cK
    c.pe
    @9
    cW
    cX
    @9
    eqid
    #
    dochoc.h
    dochoc.i
    dochoc.o
    dochvalr
    fveq2d
    @5
    @12
    @11
    @7
    cfv
    #
    @9
    cfv
    #
    cI
    cfv
    #
    cX
    @2
    @4
    @11
    @3
    wcel
    #
    @12
    @16
    wceq
    @2
    @4
    @10
    cK
    cbs
    cfv
    #
    wcel
    #
    @17
    @5
    cK
    cops
    wcel
    #
    @8
    @18
    wcel
    #
    @19
    @0
    @20
    @1
    @4
    cK
    hlop
    ad2antrr
    #
    @18
    cH
    cI
    cK
    cW
    cX
    @18
    eqid
    #
    dochoc.h
    dochoc.i
    dihcnvcl
    #
    @18
    cK
    @9
    @8
    @23
    @13
    opoccl
    syl2anc
    #
    @18
    cH
    cI
    cK
    cW
    @10
    @23
    dochoc.h
    dochoc.i
    dihcl
    syldan
    cH
    cI
    cK
    c.pe
    @9
    cW
    @11
    @13
    dochoc.h
    dochoc.i
    dochoc.o
    dochvalr
    syldan
    @5
    @16
    @8
    cI
    cfv
    cX
    @5
    @15
    @8
    cI
    @5
    @15
    @10
    @9
    cfv
    #
    @8
    @5
    @14
    @10
    @9
    @2
    @4
    @19
    @14
    @10
    wceq
    @25
    @18
    cH
    cI
    cK
    cW
    @10
    @23
    dochoc.h
    dochoc.i
    dihcnvid1
    syldan
    fveq2d
    @5
    @20
    @21
    @26
    @8
    wceq
    @22
    @24
    @18
    cK
    @9
    @8
    @23
    @13
    opococ
    syl2anc
    eqtrd
    fveq2d
    cH
    cI
    cK
    cW
    cX
    dochoc.h
    dochoc.i
    dihcnvid2
    eqtrd
    eqtrd
    eqtrd
end
