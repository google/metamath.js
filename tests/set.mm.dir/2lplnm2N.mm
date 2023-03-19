include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wne.mm"
include "co.mm"
include "simp22.mm"
include "cbs.mm"
include "cfv.mm"
include "ccvr.mm"
include "wb.mm"
include "simp1.mm"
include "clat.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "simp21.mm"
include "eqid.mm"
include "lplnbase.mm"
include "syl.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "cjn.mm"
include "2lplnj.mm"
include "simp23.mm"
include "eqeltrd.mm"
include "latlej1.mm"
include "lplncvrlvol2.mm"
include "syl31anc.mm"
include "cvrexch.mm"
include "mpbird.mm"
include "llncvrlpln.mm"

theorem 2lplnm2N
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  assume 2lplnm2.l: |- .<_ = ( le ` K )
  assume 2lplnm2.m: |- ./\ = ( meet ` K )
  assume 2lplnm2.a: |- N = ( LLines ` K )
  assume 2lplnm2.p: |- P = ( LPlanes ` K )
  assume 2lplnm2.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ ( X e. P /\ Y e. P /\ W e. V ) /\ ( X .<_ W /\ Y .<_ W /\ X =/= Y ) ) -> ( X ./\ Y ) e. N )

  proof
    cK
    chlt
    wcel
    #
    cX
    cP
    wcel
    #
    cY
    cP
    wcel
    #
    cW
    cV
    wcel
    #
    w3a
    #
    cX
    cW
    c.le
    wbr
    cY
    cW
    c.le
    wbr
    cX
    cY
    wne
    w3a
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cN
    wcel
    #
    @2
    @0
    @1
    @2
    @3
    @5
    simp22
    #
    @6
    @0
    @7
    cK
    cbs
    cfv
    #
    wcel
    #
    cY
    @10
    wcel
    #
    @7
    cY
    cK
    ccvr
    cfv
    #
    wbr
    #
    @8
    @2
    wb
    @0
    @4
    @5
    simp1
    #
    @6
    cK
    clat
    wcel
    #
    cX
    @10
    wcel
    #
    @12
    @11
    @0
    @4
    @16
    @5
    cK
    hllat
    3ad2ant1
    #
    @6
    @1
    @17
    @0
    @1
    @2
    @3
    @5
    simp21
    #
    @10
    cP
    cK
    cX
    @10
    eqid
    #
    2lplnm2.p
    lplnbase
    syl
    #
    @6
    @2
    @12
    @9
    @10
    cP
    cK
    cY
    @20
    2lplnm2.p
    lplnbase
    syl
    #
    @10
    cK
    c.an
    cX
    cY
    @20
    2lplnm2.m
    latmcl
    syl3anc
    @22
    @6
    @14
    cX
    cX
    cY
    cK
    cjn
    cfv
    #
    co
    #
    @13
    wbr
    #
    @6
    @0
    @1
    @24
    cV
    wcel
    cX
    @24
    c.le
    wbr
    #
    @25
    @15
    @19
    @6
    @24
    cW
    cV
    cP
    @23
    cK
    c.le
    cV
    cW
    cX
    cY
    2lplnm2.l
    @23
    eqid
    #
    2lplnm2.p
    2lplnm2.v
    2lplnj
    @0
    @1
    @2
    @3
    @5
    simp23
    eqeltrd
    @6
    @16
    @17
    @12
    @26
    @18
    @21
    @22
    @10
    @23
    cK
    c.le
    cX
    cY
    @20
    2lplnm2.l
    @27
    latlej1
    syl3anc
    @13
    cP
    cK
    c.le
    cV
    cX
    @24
    2lplnm2.l
    @13
    eqid
    #
    2lplnm2.p
    2lplnm2.v
    lplncvrlvol2
    syl31anc
    @6
    @0
    @17
    @12
    @14
    @25
    wb
    @15
    @21
    @22
    @10
    @13
    @23
    cK
    c.an
    cX
    cY
    @20
    @27
    2lplnm2.m
    @28
    cvrexch
    syl3anc
    mpbird
    @10
    @13
    cP
    cK
    cN
    @7
    cY
    @20
    @28
    2lplnm2.a
    2lplnm2.p
    llncvrlpln
    syl31anc
    mpbird
end
