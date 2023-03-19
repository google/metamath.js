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
include "llnbase.mm"
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
include "atcvrlln2.mm"
include "syl31anc.mm"
include "latmcl.mm"
include "3jca.mm"
include "atcvrlln.mm"
include "sylan.mm"
include "mpbird.mm"
include "impbida.mm"
include "simpl2.mm"
include "latlej1.mm"
include "llncvrlpln2.mm"
include "latjcl.mm"
include "llncvrlpln.mm"
include "mpbid.mm"
include "3bitr4d.mm"

theorem 2llnmj
  let cA: class A
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  assume 2llnmj.j: |- .\/ = ( join ` K )
  assume 2llnmj.m: |- ./\ = ( meet ` K )
  assume 2llnmj.a: |- A = ( Atoms ` K )
  assume 2llnmj.n: |- N = ( LLines ` K )
  assume 2llnmj.p: |- P = ( LPlanes ` K )


  assert |- ( ( K e. HL /\ X e. N /\ Y e. N ) -> ( ( X ./\ Y ) e. A <-> ( X .\/ Y ) e. P ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cN
    wcel
    #
    cY
    cN
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
    cA
    wcel
    #
    @7
    cP
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
    cK
    cN
    cX
    @11
    eqid
    #
    2llnmj.n
    llnbase
    #
    3ad2ant2
    #
    @2
    @0
    @13
    @1
    @11
    cK
    cN
    cY
    @15
    2llnmj.n
    llnbase
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
    2llnmj.j
    2llnmj.m
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
    2llnmj.m
    latmle2
    syl3an
    adantr
    cA
    @5
    @4
    cK
    @21
    cN
    cY
    @25
    @20
    2llnmj.a
    2llnmj.n
    atcvrlln2
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
    2llnmj.m
    latmcl
    syl3an
    @19
    3jca
    cA
    @11
    @5
    cK
    cN
    @4
    cY
    @15
    @20
    2llnmj.a
    2llnmj.n
    atcvrlln
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
    2llnmj.j
    latlej1
    syl3an
    adantr
    @5
    cP
    cK
    @21
    cN
    cX
    @7
    @25
    @20
    2llnmj.n
    2llnmj.p
    llncvrlpln2
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
    2llnmj.j
    latjcl
    syl3an
    3jca
    @11
    @5
    cP
    cK
    cN
    cX
    @7
    @15
    @20
    2llnmj.n
    2llnmj.p
    llncvrlpln
    sylan
    mpbid
    impbida
    3bitr4d
end
