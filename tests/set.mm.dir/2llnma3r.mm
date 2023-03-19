include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp23.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "simp22.mm"
include "oveq12d.mm"
include "wa.mm"
include "simpr.mm"
include "oveq2d.mm"
include "simpl1.mm"
include "simpl23.mm"
include "hlatjidm.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "wbr.mm"
include "hlatlej1.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wb.mm"
include "hllat.mm"
include "3ad2ant1.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "hlatjcl.mm"
include "latleeqm2.mm"
include "mpbid.mm"
include "adantr.mm"
include "wn.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl3.mm"
include "wi.mm"
include "hlatlej2.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "biimpd.mm"
include "mpan2d.mm"
include "ps-1.mm"
include "syl132anc.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "syld.mm"
include "necon3ad.mm"
include "mpd.mm"
include "2llnma1.mm"
include "syl131anc.mm"
include "pm2.61dane.mm"

theorem 2llnma3r
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  assume 2llnm.l: |- .<_ = ( le ` K )
  assume 2llnm.j: |- .\/ = ( join ` K )
  assume 2llnm.m: |- ./\ = ( meet ` K )
  assume 2llnm.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ ( P e. A /\ Q e. A /\ R e. A ) /\ ( P .\/ R ) =/= ( Q .\/ R ) ) -> ( ( P .\/ R ) ./\ ( Q .\/ R ) ) = R )

  proof
    cK
    chlt
    wcel
    #
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cR
    cA
    wcel
    #
    w3a
    #
    cP
    cR
    c.or
    co
    #
    cQ
    cR
    c.or
    co
    #
    wne
    #
    w3a
    #
    @5
    @6
    c.an
    co
    cR
    cP
    c.or
    co
    #
    cR
    cQ
    c.or
    co
    #
    c.an
    co
    #
    cR
    @8
    @5
    @9
    @6
    @10
    c.an
    @8
    @0
    @1
    @3
    @5
    @9
    wceq
    @0
    @4
    @7
    simp1
    #
    @0
    @1
    @2
    @3
    @7
    simp21
    #
    @0
    @1
    @2
    @3
    @7
    simp23
    #
    cA
    c.or
    cK
    cP
    cR
    2llnm.j
    2llnm.a
    hlatjcom
    syl3anc
    @8
    @0
    @2
    @3
    @6
    @10
    wceq
    @12
    @0
    @1
    @2
    @3
    @7
    simp22
    #
    @14
    cA
    c.or
    cK
    cQ
    cR
    2llnm.j
    2llnm.a
    hlatjcom
    syl3anc
    oveq12d
    @8
    @11
    cR
    wceq
    #
    cQ
    cR
    @8
    cQ
    cR
    wceq
    #
    wa
    #
    @11
    @9
    cR
    c.an
    co
    #
    cR
    @18
    @10
    cR
    @9
    c.an
    @18
    @10
    cR
    cR
    c.or
    co
    #
    cR
    @18
    cQ
    cR
    cR
    c.or
    @8
    @17
    simpr
    oveq2d
    @18
    @0
    @3
    @20
    cR
    wceq
    @0
    @4
    @7
    @17
    simpl1
    @1
    @2
    @3
    @0
    @7
    @17
    simpl23
    cA
    c.or
    cK
    cR
    2llnm.j
    2llnm.a
    hlatjidm
    syl2anc
    eqtrd
    oveq2d
    @8
    @19
    cR
    wceq
    #
    @17
    @8
    cR
    @9
    c.le
    wbr
    #
    @21
    @8
    @0
    @3
    @1
    @22
    @12
    @14
    @13
    cA
    cR
    cP
    c.or
    cK
    c.le
    2llnm.l
    2llnm.j
    2llnm.a
    hlatlej1
    syl3anc
    @8
    cK
    clat
    wcel
    #
    cR
    cK
    cbs
    cfv
    #
    wcel
    #
    @9
    @24
    wcel
    #
    @22
    @21
    wb
    @0
    @4
    @23
    @7
    cK
    hllat
    3ad2ant1
    #
    @8
    @3
    @25
    @14
    cA
    @24
    cR
    cK
    @24
    eqid
    #
    2llnm.a
    atbase
    syl
    #
    @8
    @0
    @3
    @1
    @26
    @12
    @14
    @13
    cA
    @24
    c.or
    cK
    cR
    cP
    @28
    2llnm.j
    2llnm.a
    hlatjcl
    syl3anc
    @24
    cK
    c.le
    c.an
    cR
    @9
    @28
    2llnm.l
    2llnm.m
    latleeqm2
    syl3anc
    mpbid
    adantr
    eqtrd
    @8
    cQ
    cR
    wne
    #
    wa
    #
    @0
    @1
    @3
    @2
    cQ
    @5
    c.le
    wbr
    #
    wn
    #
    @16
    @0
    @4
    @7
    @30
    simpl1
    #
    @1
    @2
    @3
    @0
    @7
    @30
    simpl21
    #
    @1
    @2
    @3
    @0
    @7
    @30
    simpl23
    #
    @1
    @2
    @3
    @0
    @7
    @30
    simpl22
    #
    @31
    @7
    @33
    @0
    @4
    @7
    @30
    simpl3
    @31
    @32
    @5
    @6
    @31
    @32
    @6
    @5
    c.le
    wbr
    #
    @5
    @6
    wceq
    #
    @8
    @32
    @38
    wi
    @30
    @8
    @32
    cR
    @5
    c.le
    wbr
    #
    @38
    @8
    @0
    @1
    @3
    @40
    @12
    @13
    @14
    cA
    cP
    cR
    c.or
    cK
    c.le
    2llnm.l
    2llnm.j
    2llnm.a
    hlatlej2
    syl3anc
    @8
    @32
    @40
    wa
    #
    @38
    @8
    @23
    cQ
    @24
    wcel
    #
    @25
    @5
    @24
    wcel
    #
    @41
    @38
    wb
    @27
    @8
    @2
    @42
    @15
    cA
    @24
    cQ
    cK
    @28
    2llnm.a
    atbase
    syl
    @29
    @8
    @0
    @1
    @3
    @43
    @12
    @13
    @14
    cA
    @24
    c.or
    cK
    cP
    cR
    @28
    2llnm.j
    2llnm.a
    hlatjcl
    syl3anc
    @24
    c.or
    cK
    c.le
    cQ
    cR
    @5
    @28
    2llnm.l
    2llnm.j
    latjle12
    syl13anc
    biimpd
    mpan2d
    adantr
    @31
    @38
    @6
    @5
    wceq
    #
    @39
    @31
    @38
    @44
    @31
    @0
    @2
    @3
    @30
    @1
    @3
    @38
    @44
    wb
    @34
    @37
    @36
    @8
    @30
    simpr
    @35
    @36
    cA
    cQ
    cR
    cP
    cR
    c.or
    cK
    c.le
    2llnm.l
    2llnm.j
    2llnm.a
    ps-1
    syl132anc
    biimpd
    @6
    @5
    eqcom
    syl6ib
    syld
    necon3ad
    mpd
    cA
    cP
    cR
    cQ
    c.or
    cK
    c.le
    c.an
    2llnm.l
    2llnm.j
    2llnm.m
    2llnm.a
    2llnma1
    syl131anc
    pm2.61dane
    eqtrd
end
