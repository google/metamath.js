include "chlt.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cp0.mm"
include "cfv.mm"
include "cbs.mm"
include "simpl11.mm"
include "simpl21.mm"
include "simpl12.mm"
include "eqid.mm"
include "llnbase.mm"
include "syl.mm"
include "clat.mm"
include "hllat.mm"
include "simpl13.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latmle1.mm"
include "atmod2i2.mm"
include "syl131anc.mm"
include "atbase.mm"
include "latmcom.mm"
include "simpl23.mm"
include "cal.mm"
include "wb.mm"
include "hlatl.mm"
include "atnle.mm"
include "mpbid.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "simpr.mm"
include "clc.mm"
include "wne.mm"
include "hlcvl.mm"
include "simpl3.mm"
include "simpl22.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "necon3bd.mm"
include "mpd.mm"
include "necomd.mm"
include "cvlatexchb1.mm"
include "oveq2d.mm"
include "3eqtr3rd.mm"
include "col.mm"
include "hlol.mm"
include "olj02.mm"
include "syl2anc.mm"
include "eqtr2d.mm"
include "ex.mm"
include "simp11.mm"
include "simp12.mm"
include "simp21.mm"
include "simp22.mm"
include "hlatjcl.mm"
include "latmle2.mm"
include "impbid.mm"

theorem llnexchb2lem
  let cA: class A
  let cP: class P
  let cQ: class Q
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cX: class X
  let cY: class Y
  assume llnexch.l: |- .<_ = ( le ` K )
  assume llnexch.j: |- .\/ = ( join ` K )
  assume llnexch.m: |- ./\ = ( meet ` K )
  assume llnexch.a: |- A = ( Atoms ` K )
  assume llnexch.n: |- N = ( LLines ` K )


  assert |- ( ( ( K e. HL /\ X e. N /\ Y e. N ) /\ ( P e. A /\ Q e. A /\ -. P .<_ X ) /\ ( X ./\ Y ) e. A ) -> ( ( X ./\ Y ) .<_ ( P .\/ Q ) <-> ( X ./\ Y ) = ( X ./\ ( P .\/ Q ) ) ) )

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
    cP
    cA
    wcel
    #
    cQ
    cA
    wcel
    #
    cP
    cX
    c.le
    wbr
    #
    wn
    #
    w3a
    #
    cX
    cY
    c.an
    co
    #
    cA
    wcel
    #
    w3a
    #
    @9
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    @9
    cX
    @12
    c.an
    co
    #
    wceq
    #
    @11
    @13
    @15
    @11
    @13
    wa
    #
    @14
    cK
    cp0
    cfv
    #
    @9
    c.or
    co
    #
    @9
    @16
    cX
    cP
    c.an
    co
    #
    @9
    c.or
    co
    #
    cX
    cP
    @9
    c.or
    co
    #
    c.an
    co
    #
    @18
    @14
    @16
    @0
    @4
    cX
    cK
    cbs
    cfv
    #
    wcel
    #
    @9
    @23
    wcel
    #
    @9
    cX
    c.le
    wbr
    #
    @20
    @22
    wceq
    @0
    @1
    @2
    @8
    @10
    @13
    simpl11
    #
    @4
    @5
    @7
    @3
    @10
    @13
    simpl21
    #
    @16
    @1
    @24
    @0
    @1
    @2
    @8
    @10
    @13
    simpl12
    @23
    cK
    cN
    cX
    @23
    eqid
    #
    llnexch.n
    llnbase
    #
    syl
    #
    @16
    cK
    clat
    wcel
    #
    @24
    cY
    @23
    wcel
    #
    @25
    @16
    @0
    @32
    @27
    cK
    hllat
    #
    syl
    #
    @31
    @16
    @2
    @33
    @0
    @1
    @2
    @8
    @10
    @13
    simpl13
    @23
    cK
    cN
    cY
    @29
    llnexch.n
    llnbase
    syl
    #
    @23
    cK
    c.an
    cX
    cY
    @29
    llnexch.m
    latmcl
    syl3anc
    #
    @16
    @32
    @24
    @33
    @26
    @35
    @31
    @36
    @23
    cK
    c.le
    c.an
    cX
    cY
    @29
    llnexch.l
    llnexch.m
    latmle1
    syl3anc
    #
    cA
    @23
    cP
    c.or
    cK
    c.le
    c.an
    cX
    @9
    @29
    llnexch.l
    llnexch.j
    llnexch.m
    llnexch.a
    atmod2i2
    syl131anc
    @16
    @19
    @17
    @9
    c.or
    @16
    @19
    cP
    cX
    c.an
    co
    #
    @17
    @16
    @32
    @24
    cP
    @23
    wcel
    #
    @19
    @39
    wceq
    @35
    @31
    @16
    @4
    @40
    @28
    cA
    @23
    cP
    cK
    @29
    llnexch.a
    atbase
    syl
    @23
    cK
    c.an
    cX
    cP
    @29
    llnexch.m
    latmcom
    syl3anc
    @16
    @7
    @39
    @17
    wceq
    #
    @4
    @5
    @7
    @3
    @10
    @13
    simpl23
    #
    @16
    cK
    cal
    wcel
    #
    @4
    @24
    @7
    @41
    wb
    @16
    @0
    @43
    @27
    cK
    hlatl
    syl
    @28
    @31
    cA
    @23
    cP
    cK
    c.le
    c.an
    cX
    @17
    @29
    llnexch.l
    llnexch.m
    @17
    eqid
    #
    llnexch.a
    atnle
    syl3anc
    mpbid
    eqtrd
    oveq1d
    @16
    @21
    @12
    cX
    c.an
    @16
    @13
    @21
    @12
    wceq
    #
    @11
    @13
    simpr
    @16
    cK
    clc
    wcel
    #
    @10
    @5
    @4
    @9
    cP
    wne
    @13
    @45
    wb
    @16
    @0
    @46
    @27
    cK
    hlcvl
    syl
    @3
    @8
    @10
    @13
    simpl3
    @4
    @5
    @7
    @3
    @10
    @13
    simpl22
    @28
    @16
    cP
    @9
    @16
    @7
    cP
    @9
    wne
    @42
    @16
    @6
    cP
    @9
    @16
    @6
    cP
    @9
    wceq
    @26
    @38
    cP
    @9
    cX
    c.le
    breq1
    syl5ibrcom
    necon3bd
    mpd
    necomd
    cA
    @9
    cQ
    cP
    c.or
    cK
    c.le
    llnexch.l
    llnexch.j
    llnexch.a
    cvlatexchb1
    syl131anc
    mpbid
    oveq2d
    3eqtr3rd
    @16
    cK
    col
    wcel
    #
    @25
    @18
    @9
    wceq
    @16
    @0
    @47
    @27
    cK
    hlol
    syl
    @37
    @23
    c.or
    cK
    @9
    @17
    @29
    llnexch.j
    @44
    olj02
    syl2anc
    eqtr2d
    ex
    @11
    @13
    @15
    @14
    @12
    c.le
    wbr
    #
    @11
    @32
    @24
    @12
    @23
    wcel
    #
    @48
    @11
    @0
    @32
    @0
    @1
    @2
    @8
    @10
    simp11
    #
    @34
    syl
    @11
    @1
    @24
    @0
    @1
    @2
    @8
    @10
    simp12
    @30
    syl
    @11
    @0
    @4
    @5
    @49
    @50
    @3
    @4
    @5
    @7
    @10
    simp21
    @3
    @4
    @5
    @7
    @10
    simp22
    cA
    @23
    c.or
    cK
    cP
    cQ
    @29
    llnexch.j
    llnexch.a
    hlatjcl
    syl3anc
    @23
    cK
    c.le
    c.an
    cX
    @12
    @29
    llnexch.l
    llnexch.m
    latmle2
    syl3anc
    @9
    @14
    @12
    c.le
    breq1
    syl5ibrcom
    impbid
end
