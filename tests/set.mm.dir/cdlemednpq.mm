include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wne.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp23l.mm"
include "simp31l.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simp23r.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "wceq.mm"
include "adantr.mm"
include "latmle1.mm"
include "simpr.mm"
include "wb.mm"
include "simp31r.mm"
include "simp32.mm"
include "simp33.mm"
include "cdlemeda.mm"
include "syl223anc.mm"
include "atbase.mm"
include "simp21.mm"
include "simp22.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cp0.mm"
include "cal.mm"
include "hlatl.mm"
include "atnle.mm"
include "mpbid.mm"
include "oveq2d.mm"
include "atmod1i1.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "olj01.mm"
include "3eqtr3d.mm"
include "breqtrd.mm"
include "ex.mm"
include "atcmp.mm"
include "sylibd.mm"
include "necon3ad.mm"
include "mpd.mm"

theorem cdlemednpq
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemeda.l: |- .<_ = ( le ` K )
  assume cdlemeda.j: |- .\/ = ( join ` K )
  assume cdlemeda.m: |- ./\ = ( meet ` K )
  assume cdlemeda.a: |- A = ( Atoms ` K )
  assume cdlemeda.h: |- H = ( LHyp ` K )
  assume cdlemeda.d: |- D = ( ( R .\/ S ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ Q e. A /\ ( R e. A /\ -. R .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> -. D .<_ ( P .\/ Q ) )

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
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    @12
    c.le
    wbr
    wn
    #
    w3a
    #
    w3a
    #
    cD
    cR
    wne
    #
    cD
    @12
    c.le
    wbr
    #
    wn
    @16
    cD
    cW
    c.le
    wbr
    @6
    @17
    @16
    cD
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdlemeda.d
    @16
    cK
    clat
    wcel
    #
    @19
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @22
    wcel
    #
    @20
    cW
    c.le
    wbr
    @16
    @0
    @21
    @0
    @1
    @8
    @15
    simp1l
    #
    cK
    hllat
    syl
    #
    @16
    @0
    @5
    @9
    @23
    @25
    @5
    @6
    @3
    @4
    @2
    @15
    simp23l
    #
    @9
    @10
    @13
    @14
    @2
    @8
    simp31l
    #
    cA
    @22
    c.or
    cK
    cR
    cS
    @22
    eqid
    #
    cdlemeda.j
    cdlemeda.a
    hlatjcl
    syl3anc
    #
    @16
    @1
    @24
    @0
    @1
    @8
    @15
    simp1r
    #
    @22
    cH
    cK
    cW
    @29
    cdlemeda.h
    lhpbase
    syl
    #
    @22
    cK
    c.le
    c.an
    @19
    cW
    @29
    cdlemeda.l
    cdlemeda.m
    latmle2
    syl3anc
    syl5eqbr
    @5
    @6
    @3
    @4
    @2
    @15
    simp23r
    cD
    cR
    cW
    c.le
    nbrne2
    syl2anc
    @16
    @18
    cD
    cR
    @16
    @18
    cD
    cR
    c.le
    wbr
    #
    cD
    cR
    wceq
    #
    @16
    @18
    @33
    @16
    @18
    wa
    #
    cD
    @19
    @12
    c.an
    co
    #
    cR
    c.le
    @35
    cD
    @19
    c.le
    wbr
    #
    @18
    cD
    @36
    c.le
    wbr
    #
    @35
    cD
    @20
    @19
    c.le
    cdlemeda.d
    @35
    @21
    @23
    @24
    @20
    @19
    c.le
    wbr
    @16
    @21
    @18
    @26
    adantr
    #
    @16
    @23
    @18
    @30
    adantr
    #
    @16
    @24
    @18
    @32
    adantr
    @22
    cK
    c.le
    c.an
    @19
    cW
    @29
    cdlemeda.l
    cdlemeda.m
    latmle1
    syl3anc
    syl5eqbr
    @16
    @18
    simpr
    @35
    @21
    cD
    @22
    wcel
    #
    @23
    @12
    @22
    wcel
    #
    @37
    @18
    wa
    @38
    wb
    @39
    @16
    @41
    @18
    @16
    cD
    cA
    wcel
    #
    @41
    @16
    @0
    @1
    @9
    @10
    @5
    @13
    @14
    @43
    @25
    @31
    @28
    @9
    @10
    @13
    @14
    @2
    @8
    simp31r
    @27
    @2
    @8
    @11
    @13
    @14
    simp32
    #
    @2
    @8
    @11
    @13
    @14
    simp33
    #
    cA
    cD
    cP
    cQ
    cR
    cS
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemeda.l
    cdlemeda.j
    cdlemeda.m
    cdlemeda.a
    cdlemeda.h
    cdlemeda.d
    cdlemeda
    syl223anc
    #
    cA
    @22
    cD
    cK
    @29
    cdlemeda.a
    atbase
    syl
    adantr
    @40
    @16
    @42
    @18
    @16
    @0
    @3
    @4
    @42
    @25
    @2
    @3
    @4
    @7
    @15
    simp21
    @2
    @3
    @4
    @7
    @15
    simp22
    cA
    @22
    c.or
    cK
    cP
    cQ
    @29
    cdlemeda.j
    cdlemeda.a
    hlatjcl
    syl3anc
    #
    adantr
    @22
    cK
    c.le
    c.an
    cD
    @19
    @12
    @29
    cdlemeda.l
    cdlemeda.m
    latlem12
    syl13anc
    mpbi2and
    @16
    @36
    cR
    wceq
    @18
    @16
    cR
    cS
    @12
    c.an
    co
    #
    c.or
    co
    #
    cR
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    @36
    cR
    @16
    @48
    @50
    cR
    c.or
    @16
    @14
    @48
    @50
    wceq
    #
    @45
    @16
    cK
    cal
    wcel
    #
    @9
    @42
    @14
    @52
    wb
    @16
    @0
    @53
    @25
    cK
    hlatl
    syl
    #
    @28
    @47
    cA
    @22
    cS
    cK
    c.le
    c.an
    @12
    @50
    @29
    cdlemeda.l
    cdlemeda.m
    @50
    eqid
    #
    cdlemeda.a
    atnle
    syl3anc
    mpbid
    oveq2d
    @16
    @0
    @5
    cS
    @22
    wcel
    #
    @42
    @13
    @49
    @36
    wceq
    @25
    @27
    @16
    @9
    @56
    @28
    cA
    @22
    cS
    cK
    @29
    cdlemeda.a
    atbase
    syl
    @47
    @44
    cA
    @22
    cR
    c.or
    cK
    c.le
    c.an
    cS
    @12
    @29
    cdlemeda.l
    cdlemeda.j
    cdlemeda.m
    cdlemeda.a
    atmod1i1
    syl131anc
    @16
    cK
    col
    wcel
    #
    cR
    @22
    wcel
    #
    @51
    cR
    wceq
    @16
    @0
    @57
    @25
    cK
    hlol
    syl
    @16
    @5
    @58
    @27
    cA
    @22
    cR
    cK
    @29
    cdlemeda.a
    atbase
    syl
    @22
    c.or
    cK
    cR
    @50
    @29
    cdlemeda.j
    @55
    olj01
    syl2anc
    3eqtr3d
    adantr
    breqtrd
    ex
    @16
    @53
    @43
    @5
    @33
    @34
    wb
    @54
    @46
    @27
    cA
    cD
    cR
    cK
    c.le
    cdlemeda.l
    cdlemeda.a
    atcmp
    syl3anc
    sylibd
    necon3ad
    mpd
end
