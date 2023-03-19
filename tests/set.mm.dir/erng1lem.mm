include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "cres.mm"
include "cbs.mm"
include "cfv.mm"
include "cv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "cur.mm"
include "tendoidcl.mm"
include "eqid.mm"
include "erngbase.mm"
include "eleqtrrd.mm"
include "eleq2d.mm"
include "ccom.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "erngmul.mm"
include "syl12anc.mm"
include "tendo1mul.mm"
include "eqtrd.mm"
include "tendo1mulr.mm"
include "jca.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimiv.mm"
include "crg.mm"
include "wb.mm"
include "isringid.mm"
include "syl.mm"
include "mpbi2and.mm"

theorem erng1lem
  let cD: class D
  let cT: class T
  let cE: class E
  let cH: class H
  let cK: class K
  let cW: class W
  let vu: setvar u
  assume erng1.h: |- H = ( LHyp ` K )
  assume erng1.t: |- T = ( ( LTrn ` K ) ` W )
  assume erng1.e: |- E = ( ( TEndo ` K ) ` W )
  assume erng1.d: |- D = ( ( EDRing ` K ) ` W )
  assume erng1.r: |- ( ( K e. HL /\ W e. H ) -> D e. Ring )


  assert |- ( ( K e. HL /\ W e. H ) -> ( 1r ` D ) = ( _I |` T ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cid
    cT
    cres
    #
    cD
    cbs
    cfv
    #
    wcel
    #
    @1
    vu
    cv
    #
    cD
    cmulr
    cfv
    #
    co
    #
    @4
    wceq
    #
    @4
    @1
    @5
    co
    #
    @4
    wceq
    #
    wa
    #
    vu
    @2
    wral
    #
    cD
    cur
    cfv
    #
    @1
    wceq
    #
    @0
    @1
    cE
    @2
    cT
    cE
    cH
    cK
    cW
    erng1.h
    erng1.t
    erng1.e
    tendoidcl
    #
    @2
    cD
    cT
    cE
    cH
    cK
    chlt
    cW
    erng1.h
    erng1.t
    erng1.e
    erng1.d
    @2
    eqid
    #
    erngbase
    #
    eleqtrrd
    @0
    @10
    vu
    @2
    @0
    @4
    @2
    wcel
    @4
    cE
    wcel
    #
    @10
    @0
    @2
    cE
    @4
    @16
    eleq2d
    @0
    @17
    @10
    @0
    @17
    wa
    #
    @7
    @9
    @18
    @6
    @1
    @4
    ccom
    #
    @4
    @18
    @0
    @1
    cE
    wcel
    #
    @17
    @6
    @19
    wceq
    @0
    @17
    simpl
    #
    @0
    @20
    @17
    @14
    adantr
    #
    @0
    @17
    simpr
    #
    cD
    cT
    @5
    @1
    cE
    cH
    cK
    @4
    cW
    chlt
    erng1.h
    erng1.t
    erng1.e
    erng1.d
    @5
    eqid
    #
    erngmul
    syl12anc
    cT
    @4
    cE
    cH
    cK
    cW
    erng1.h
    erng1.t
    erng1.e
    tendo1mul
    eqtrd
    @18
    @8
    @4
    @1
    ccom
    #
    @4
    @18
    @0
    @17
    @20
    @8
    @25
    wceq
    @21
    @23
    @22
    cD
    cT
    @5
    @4
    cE
    cH
    cK
    @1
    cW
    chlt
    erng1.h
    erng1.t
    erng1.e
    erng1.d
    @24
    erngmul
    syl12anc
    cT
    @4
    cE
    cH
    cK
    cW
    erng1.h
    erng1.t
    erng1.e
    tendo1mulr
    eqtrd
    jca
    ex
    sylbid
    ralrimiv
    @0
    cD
    crg
    wcel
    @3
    @11
    wa
    @13
    wb
    erng1.r
    vu
    @2
    cD
    @5
    @12
    @1
    @15
    @24
    @12
    eqid
    isringid
    syl
    mpbi2and
end
