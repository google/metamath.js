include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wbr.mm"
include "cp0.mm"
include "wceq.mm"
include "cal.mm"
include "catm.mm"
include "wne.mm"
include "hlatl.mm"
include "adantr.mm"
include "simpr.mm"
include "cbs.mm"
include "wb.mm"
include "eqid.mm"
include "lhpbase.mm"
include "lhpoc.mm"
include "sylan2.mm"
include "mpbid.mm"
include "atn0.mm"
include "syl2anc.mm"
include "neneqd.mm"
include "cmee.mm"
include "co.mm"
include "clat.mm"
include "hllat.mm"
include "ad2antrr.mm"
include "cops.mm"
include "hlop.mm"
include "ad2antlr.mm"
include "opoccl.mm"
include "latref.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "opnoncon.mm"
include "breqtrd.mm"
include "ople0.mm"
include "mtand.mm"

theorem lhpocnle
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let c.pe: class ._|_
  let cW: class W
  assume lhpocnle.l: |- .<_ = ( le ` K )
  assume lhpocnle.o: |- ._|_ = ( oc ` K )
  assume lhpocnle.h: |- H = ( LHyp ` K )


  assert |- ( ( K e. HL /\ W e. H ) -> -. ( ._|_ ` W ) .<_ W )

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
    cW
    c.pe
    cfv
    #
    cW
    c.le
    wbr
    #
    @3
    cK
    cp0
    cfv
    #
    wceq
    #
    @2
    @3
    @5
    @2
    cK
    cal
    wcel
    #
    @3
    cK
    catm
    cfv
    #
    wcel
    #
    @3
    @5
    wne
    @0
    @7
    @1
    cK
    hlatl
    adantr
    @2
    @1
    @9
    @0
    @1
    simpr
    @1
    @0
    cW
    cK
    cbs
    cfv
    #
    wcel
    #
    @1
    @9
    wb
    @10
    cH
    cK
    cW
    @10
    eqid
    #
    lhpocnle.h
    lhpbase
    #
    @8
    @10
    cH
    cK
    c.pe
    cW
    @12
    lhpocnle.o
    @8
    eqid
    #
    lhpocnle.h
    lhpoc
    sylan2
    mpbid
    @8
    @3
    cK
    @5
    @5
    eqid
    #
    @14
    atn0
    syl2anc
    neneqd
    @2
    @4
    wa
    #
    @3
    @5
    c.le
    wbr
    #
    @6
    @16
    @3
    cW
    @3
    cK
    cmee
    cfv
    #
    co
    #
    @5
    c.le
    @16
    @4
    @3
    @3
    c.le
    wbr
    #
    @3
    @19
    c.le
    wbr
    #
    @2
    @4
    simpr
    @16
    cK
    clat
    wcel
    #
    @3
    @10
    wcel
    #
    @20
    @0
    @22
    @1
    @4
    cK
    hllat
    ad2antrr
    #
    @16
    cK
    cops
    wcel
    #
    @11
    @23
    @0
    @25
    @1
    @4
    cK
    hlop
    ad2antrr
    #
    @1
    @11
    @0
    @4
    @13
    ad2antlr
    #
    @10
    cK
    c.pe
    cW
    @12
    lhpocnle.o
    opoccl
    syl2anc
    #
    @10
    cK
    c.le
    @3
    @12
    lhpocnle.l
    latref
    syl2anc
    @16
    @22
    @23
    @11
    @23
    @4
    @20
    wa
    @21
    wb
    @24
    @28
    @27
    @28
    @10
    cK
    c.le
    @18
    @3
    cW
    @3
    @12
    lhpocnle.l
    @18
    eqid
    #
    latlem12
    syl13anc
    mpbi2and
    @16
    @25
    @11
    @19
    @5
    wceq
    @26
    @27
    @10
    cK
    @18
    c.pe
    cW
    @5
    @12
    lhpocnle.o
    @29
    @15
    opnoncon
    syl2anc
    breqtrd
    @16
    @25
    @23
    @17
    @6
    wb
    @26
    @28
    @10
    cK
    c.le
    @3
    @5
    @12
    lhpocnle.l
    @15
    ople0
    syl2anc
    mpbid
    mtand
end
