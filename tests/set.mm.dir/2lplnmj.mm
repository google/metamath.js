include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "ccvr.mm"
include "cfv.mm"
include "wbr.mm"
include "cbs.mm"
include "wb.mm"
include "simp1.mm"
include "eqid.mm"
include "lplnbase.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "cvrexch.mm"
include "syl3anc.mm"
include "wa.mm"
include "cple.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl3.mm"
include "clat.mm"
include "hllat.mm"
include "latmle2.mm"
include "syl3an.mm"
include "adantr.mm"
include "llncvrlpln2.mm"
include "syl31anc.mm"
include "latmcl.mm"
include "3jca.mm"
include "llncvrlpln.mm"
include "sylan.mm"
include "mpbird.mm"
include "impbida.mm"
include "simpl2.mm"
include "latlej1.mm"
include "lplncvrlvol2.mm"
include "latjcl.mm"
include "lplncvrlvol.mm"
include "mpbid.mm"
include "3bitr4d.mm"

theorem 2lplnmj
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  assume 2lplnmj.j: |- .\/ = ( join ` K )
  assume 2lplnmj.m: |- ./\ = ( meet ` K )
  assume 2lplnmj.n: |- N = ( LLines ` K )
  assume 2lplnmj.p: |- P = ( LPlanes ` K )
  assume 2lplnmj.v: |- V = ( LVols ` K )


  assert |- ( ( K e. HL /\ X e. P /\ Y e. P ) -> ( ( X ./\ Y ) e. N <-> ( X .\/ Y ) e. V ) )

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
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cY
    cK
    ccvr
    cfv
    #
    wbr
    #
    cX
    cX
    cY
    c.or
    co
    #
    @5
    wbr
    #
    @4
    cN
    wcel
    #
    @7
    cV
    wcel
    #
    @3
    @0
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    cY
    @11
    wcel
    #
    @6
    @8
    wb
    @0
    @1
    @2
    simp1
    #
    @1
    @0
    @12
    @2
    @11
    cP
    cK
    cX
    @11
    eqid
    #
    2lplnmj.p
    lplnbase
    #
    3ad2ant2
    #
    @2
    @0
    @13
    @1
    @11
    cP
    cK
    cY
    @15
    2lplnmj.p
    lplnbase
    #
    3ad2ant3
    #
    @11
    @5
    c.or
    cK
    c.an
    cX
    cY
    @15
    2lplnmj.j
    2lplnmj.m
    @5
    eqid
    #
    cvrexch
    syl3anc
    @3
    @9
    @6
    @3
    @9
    wa
    @0
    @9
    @2
    @4
    cY
    cK
    cple
    cfv
    #
    wbr
    #
    @6
    @0
    @1
    @2
    @9
    simpl1
    @3
    @9
    simpr
    @0
    @1
    @2
    @9
    simpl3
    @3
    @22
    @9
    @0
    cK
    clat
    wcel
    #
    @1
    @12
    @2
    @13
    @22
    cK
    hllat
    #
    @16
    @18
    @11
    cK
    @21
    c.an
    cX
    cY
    @15
    @21
    eqid
    #
    2lplnmj.m
    latmle2
    syl3an
    adantr
    @5
    cP
    cK
    @21
    cN
    @4
    cY
    @25
    @20
    2lplnmj.n
    2lplnmj.p
    llncvrlpln2
    syl31anc
    @3
    @6
    wa
    @9
    @2
    @0
    @1
    @2
    @6
    simpl3
    @3
    @0
    @4
    @11
    wcel
    #
    @13
    w3a
    @6
    @9
    @2
    wb
    @3
    @0
    @26
    @13
    @14
    @0
    @23
    @1
    @12
    @2
    @13
    @26
    @24
    @16
    @18
    @11
    cK
    c.an
    cX
    cY
    @15
    2lplnmj.m
    latmcl
    syl3an
    @19
    3jca
    @11
    @5
    cP
    cK
    cN
    @4
    cY
    @15
    @20
    2lplnmj.n
    2lplnmj.p
    llncvrlpln
    sylan
    mpbird
    impbida
    @3
    @10
    @8
    @3
    @10
    wa
    @0
    @1
    @10
    cX
    @7
    @21
    wbr
    #
    @8
    @0
    @1
    @2
    @10
    simpl1
    @0
    @1
    @2
    @10
    simpl2
    @3
    @10
    simpr
    @3
    @27
    @10
    @0
    @23
    @1
    @12
    @2
    @13
    @27
    @24
    @16
    @18
    @11
    c.or
    cK
    @21
    cX
    cY
    @15
    @25
    2lplnmj.j
    latlej1
    syl3an
    adantr
    @5
    cP
    cK
    @21
    cV
    cX
    @7
    @25
    @20
    2lplnmj.p
    2lplnmj.v
    lplncvrlvol2
    syl31anc
    @3
    @8
    wa
    @1
    @10
    @0
    @1
    @2
    @8
    simpl2
    @3
    @0
    @12
    @7
    @11
    wcel
    #
    w3a
    @8
    @1
    @10
    wb
    @3
    @0
    @12
    @28
    @14
    @17
    @0
    @23
    @1
    @12
    @2
    @13
    @28
    @24
    @16
    @18
    @11
    c.or
    cK
    cX
    cY
    @15
    2lplnmj.j
    latjcl
    syl3an
    3jca
    @11
    @5
    cP
    cK
    cV
    cX
    @7
    @15
    @20
    2lplnmj.p
    2lplnmj.v
    lplncvrlvol
    sylan
    mpbid
    impbida
    3bitr4d
end
