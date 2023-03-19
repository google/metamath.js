include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
include "wrel.mm"
include "cbs.mm"
include "eqid.mm"
include "dihdm.mm"
include "eleq2d.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cltrn.mm"
include "ctendo.mm"
include "cdvh.mm"
include "dihss.mm"
include "wceq.mm"
include "dvhvbase.mm"
include "adantr.mm"
include "sseqtrd.mm"
include "xpss.mm"
include "syl6ss.mm"
include "df-rel.mm"
include "sylibr.mm"
include "ex.mm"
include "sylbid.mm"
include "wn.mm"
include "c0.mm"
include "rel0.mm"
include "ndmfv.mm"
include "releqd.mm"
include "mpbiri.mm"
include "pm2.61d1.mm"

theorem dihvalrel
  let cH: class H
  let cI: class I
  let cK: class K
  let cW: class W
  let cX: class X
  assume dihvalrel.h: |- H = ( LHyp ` K )
  assume dihvalrel.i: |- I = ( ( DIsoH ` K ) ` W )


  assert |- ( ( K e. HL /\ W e. H ) -> Rel ( I ` X ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cX
    cI
    cdm
    #
    wcel
    #
    cX
    cI
    cfv
    #
    wrel
    #
    @0
    @2
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @4
    @0
    @1
    @5
    cX
    @5
    cH
    cI
    cK
    cW
    @5
    eqid
    #
    dihvalrel.h
    dihvalrel.i
    dihdm
    eleq2d
    @0
    @6
    @4
    @0
    @6
    wa
    #
    @3
    cvv
    cvv
    cxp
    #
    wss
    @4
    @8
    @3
    cW
    cK
    cltrn
    cfv
    cfv
    #
    cW
    cK
    ctendo
    cfv
    cfv
    #
    cxp
    #
    @9
    @8
    @3
    cW
    cK
    cdvh
    cfv
    cfv
    #
    cbs
    cfv
    #
    @12
    @5
    @13
    cH
    cI
    cK
    @14
    cW
    cX
    @7
    dihvalrel.h
    dihvalrel.i
    @13
    eqid
    #
    @14
    eqid
    #
    dihss
    @0
    @14
    @12
    wceq
    @6
    @10
    @13
    @11
    cH
    cK
    @14
    cW
    chlt
    dihvalrel.h
    @10
    eqid
    @11
    eqid
    @15
    @16
    dvhvbase
    adantr
    sseqtrd
    @10
    @11
    xpss
    syl6ss
    @3
    df-rel
    sylibr
    ex
    sylbid
    @2
    wn
    #
    @4
    c0
    wrel
    rel0
    @17
    @3
    c0
    cX
    cI
    ndmfv
    releqd
    mpbiri
    pm2.61d1
end
