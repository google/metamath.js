include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "ccvr.mm"
include "cfv.mm"
include "clpl.mm"
include "wrex.mm"
include "wi.mm"
include "simp2.mm"
include "cbs.mm"
include "wb.mm"
include "simp1.mm"
include "eqid.mm"
include "lvolbase.mm"
include "3ad2ant2.mm"
include "islvol4.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "wa.mm"
include "simpr3.mm"
include "cpo.mm"
include "hlpos.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "simpl3.mm"
include "syl.mm"
include "simpr1.mm"
include "lplnbase.mm"
include "simpr2.mm"
include "simpl1.mm"
include "cvrle.mm"
include "syl31anc.mm"
include "postr.mm"
include "syl13anc.mm"
include "mp2and.mm"
include "lplncvrlvol2.mm"
include "cvrcmp.mm"
include "syl132anc.mm"
include "3exp2.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "posref.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem lvolcmp
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  let vz: setvar z
  assume lvolcmp.l: |- .<_ = ( le ` K )
  assume lvolcmp.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ X e. V /\ Y e. V ) -> ( X .<_ Y <-> X = Y ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cV
    wcel
    #
    cY
    cV
    wcel
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    cX
    cY
    wceq
    #
    @3
    vz
    cv
    #
    cX
    cK
    ccvr
    cfv
    #
    wbr
    #
    vz
    cK
    clpl
    cfv
    #
    wrex
    #
    @4
    @5
    wi
    #
    @3
    @1
    @10
    @0
    @1
    @2
    simp2
    @3
    @0
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @1
    @10
    wb
    @0
    @1
    @2
    simp1
    @1
    @0
    @13
    @2
    @12
    cK
    cV
    cX
    @12
    eqid
    #
    lvolcmp.v
    lvolbase
    3ad2ant2
    #
    vz
    chlt
    @12
    @7
    @9
    cK
    cV
    cX
    @14
    @7
    eqid
    #
    @9
    eqid
    #
    lvolcmp.v
    islvol4
    syl2anc
    mpbid
    @3
    @8
    @11
    vz
    @9
    @3
    @6
    @9
    wcel
    #
    @8
    @4
    @5
    @3
    @18
    @8
    @4
    w3a
    #
    wa
    #
    @4
    @5
    @3
    @18
    @8
    @4
    simpr3
    #
    @20
    cK
    cpo
    wcel
    #
    @13
    cY
    @12
    wcel
    #
    @6
    @12
    wcel
    #
    @8
    @6
    cY
    @7
    wbr
    #
    @4
    @5
    wb
    @3
    @22
    @19
    @0
    @1
    @22
    @2
    cK
    hlpos
    3ad2ant1
    #
    adantr
    #
    @3
    @13
    @19
    @15
    adantr
    #
    @20
    @2
    @23
    @0
    @1
    @2
    @19
    simpl3
    #
    @12
    cK
    cV
    cY
    @14
    lvolcmp.v
    lvolbase
    syl
    #
    @20
    @18
    @24
    @3
    @18
    @8
    @4
    simpr1
    #
    @12
    @9
    cK
    @6
    @14
    @17
    lplnbase
    syl
    #
    @3
    @18
    @8
    @4
    simpr2
    #
    @20
    @0
    @18
    @2
    @6
    cY
    c.le
    wbr
    #
    @25
    @0
    @1
    @2
    @19
    simpl1
    #
    @31
    @29
    @20
    @6
    cX
    c.le
    wbr
    #
    @4
    @34
    @20
    @0
    @24
    @13
    @8
    @36
    @35
    @32
    @28
    @33
    chlt
    @12
    @7
    cK
    c.le
    @6
    cX
    @14
    lvolcmp.l
    @16
    cvrle
    syl31anc
    @21
    @20
    @22
    @24
    @13
    @23
    @36
    @4
    wa
    @34
    wi
    @27
    @32
    @28
    @30
    @12
    cK
    c.le
    @6
    cX
    cY
    @14
    lvolcmp.l
    postr
    syl13anc
    mp2and
    @7
    @9
    cK
    c.le
    cV
    @6
    cY
    lvolcmp.l
    @16
    @17
    lvolcmp.v
    lplncvrlvol2
    syl31anc
    @12
    @7
    cK
    c.le
    cX
    cY
    @6
    @14
    lvolcmp.l
    @16
    cvrcmp
    syl132anc
    mpbid
    3exp2
    rexlimdv
    mpd
    @3
    cX
    cX
    c.le
    wbr
    #
    @5
    @4
    @3
    @22
    @13
    @37
    @26
    @15
    @12
    cK
    c.le
    cX
    @14
    lvolcmp.l
    posref
    syl2anc
    cX
    cY
    cX
    c.le
    breq2
    syl5ibcom
    impbid
end
