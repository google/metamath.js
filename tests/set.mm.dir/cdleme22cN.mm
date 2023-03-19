include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp12l.mm"
include "simp13.mm"
include "eqid.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "simp21r.mm"
include "nbrne2.mm"
include "syl2anc.mm"
include "wceq.mm"
include "simp32l.mm"
include "adantr.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simp31l.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simpr.mm"
include "cdleme22aa.mm"
include "syl233anc.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "simp32r.mm"
include "wb.mm"
include "simp21l.mm"
include "atbase.mm"
include "simp22.mm"
include "simp12r.mm"
include "lhpat.mm"
include "syl222anc.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "cp0.mm"
include "simp31r.mm"
include "3jca.mm"
include "simp33.mm"
include "cdleme22b.mm"
include "syl232anc.mm"
include "cal.mm"
include "hlatl.mm"
include "atnle.mm"
include "mpbid.mm"
include "oveq1d.mm"
include "latmle1.mm"
include "atmod4i1.mm"
include "syl131anc.mm"
include "col.mm"
include "hlol.mm"
include "latmcl.mm"
include "olj02.mm"
include "3eqtr3d.mm"
include "atcmp.mm"
include "eqcomd.mm"
include "ex.mm"
include "necon3ad.mm"
include "mpd.mm"

theorem cdleme22cN
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let cT: class T
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cW: class W
  assume cdleme22.l: |- .<_ = ( le ` K )
  assume cdleme22.j: |- .\/ = ( join ` K )
  assume cdleme22.m: |- ./\ = ( meet ` K )
  assume cdleme22.a: |- A = ( Atoms ` K )
  assume cdleme22.h: |- H = ( LHyp ` K )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ Q e. A ) /\ ( ( S e. A /\ -. S .<_ W ) /\ T e. A /\ ( V e. A /\ V .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( S .<_ ( T .\/ V ) /\ S .<_ ( P .\/ Q ) ) /\ ( T .\/ V ) =/= ( P .\/ Q ) ) ) -> -. V .<_ ( P .\/ Q ) )

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
    cP
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cA
    wcel
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
    cT
    cA
    wcel
    #
    cV
    cA
    wcel
    #
    cV
    cW
    c.le
    wbr
    #
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    cT
    wne
    #
    wa
    #
    cS
    cT
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    @19
    @21
    wne
    #
    w3a
    #
    w3a
    #
    @21
    cW
    c.an
    co
    #
    cS
    wne
    #
    cV
    @21
    c.le
    wbr
    #
    wn
    @26
    @27
    cW
    c.le
    wbr
    #
    @9
    @28
    @26
    cK
    clat
    wcel
    #
    @21
    cK
    cbs
    cfv
    #
    wcel
    #
    cW
    @32
    wcel
    #
    @30
    @26
    @0
    @31
    @0
    @1
    @5
    @6
    @15
    @25
    simp11l
    #
    cK
    hllat
    syl
    #
    @26
    @0
    @3
    @6
    @33
    @35
    @3
    @4
    @2
    @6
    @15
    @25
    simp12l
    #
    @2
    @5
    @6
    @15
    @25
    simp13
    #
    cA
    @32
    c.or
    cK
    cP
    cQ
    @32
    eqid
    #
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    #
    @26
    @1
    @34
    @0
    @1
    @5
    @6
    @15
    @25
    simp11r
    #
    @32
    cH
    cK
    cW
    @39
    cdleme22.h
    lhpbase
    syl
    #
    @32
    cK
    c.le
    c.an
    @21
    cW
    @39
    cdleme22.l
    cdleme22.m
    latmle2
    syl3anc
    @8
    @9
    @11
    @14
    @7
    @25
    simp21r
    @27
    cS
    cW
    c.le
    nbrne2
    syl2anc
    @26
    @29
    @27
    cS
    @26
    @29
    @27
    cS
    wceq
    @26
    @29
    wa
    #
    cS
    @27
    @43
    cS
    @27
    c.le
    wbr
    #
    cS
    @27
    wceq
    #
    @43
    cS
    cT
    @27
    c.or
    co
    #
    @21
    c.an
    co
    #
    @27
    c.le
    @43
    cS
    @46
    c.le
    wbr
    #
    @22
    cS
    @47
    c.le
    wbr
    #
    @43
    cS
    @19
    @46
    c.le
    @26
    @20
    @29
    @20
    @22
    @18
    @24
    @7
    @15
    simp32l
    #
    adantr
    @43
    cV
    @27
    cT
    c.or
    @43
    @0
    @1
    @5
    @6
    @16
    @12
    @13
    @29
    cV
    @27
    wceq
    @26
    @0
    @29
    @35
    adantr
    @26
    @1
    @29
    @41
    adantr
    @2
    @5
    @6
    @15
    @25
    @29
    simpl12
    @2
    @5
    @6
    @15
    @25
    @29
    simpl13
    @26
    @16
    @29
    @16
    @17
    @23
    @24
    @7
    @15
    simp31l
    #
    adantr
    @26
    @12
    @29
    @12
    @13
    @10
    @11
    @7
    @25
    simp23l
    #
    adantr
    @26
    @13
    @29
    @12
    @13
    @10
    @11
    @7
    @25
    simp23r
    adantr
    @26
    @29
    simpr
    cA
    cP
    cQ
    @27
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    @27
    eqid
    cdleme22aa
    syl233anc
    oveq2d
    breqtrd
    @26
    @22
    @29
    @20
    @22
    @18
    @24
    @7
    @15
    simp32r
    #
    adantr
    @26
    @48
    @22
    wa
    @49
    wb
    #
    @29
    @26
    @31
    cS
    @32
    wcel
    #
    @46
    @32
    wcel
    #
    @33
    @54
    @36
    @26
    @8
    @55
    @8
    @9
    @11
    @14
    @7
    @25
    simp21l
    #
    cA
    @32
    cS
    cK
    @39
    cdleme22.a
    atbase
    syl
    @26
    @0
    @11
    @27
    cA
    wcel
    #
    @56
    @35
    @7
    @10
    @11
    @14
    @25
    simp22
    #
    @26
    @0
    @1
    @3
    @4
    @6
    @16
    @58
    @35
    @41
    @37
    @3
    @4
    @2
    @6
    @15
    @25
    simp12r
    @38
    @51
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    lhpat
    syl222anc
    #
    cA
    @32
    c.or
    cK
    cT
    @27
    @39
    cdleme22.j
    cdleme22.a
    hlatjcl
    syl3anc
    @40
    @32
    cK
    c.le
    c.an
    cS
    @46
    @21
    @39
    cdleme22.l
    cdleme22.m
    latlem12
    syl13anc
    adantr
    mpbi2and
    @26
    @47
    @27
    wceq
    @29
    @26
    cT
    @21
    c.an
    co
    #
    @27
    c.or
    co
    #
    cK
    cp0
    cfv
    #
    @27
    c.or
    co
    #
    @47
    @27
    @26
    @61
    @63
    @27
    c.or
    @26
    cT
    @21
    c.le
    wbr
    wn
    #
    @61
    @63
    wceq
    #
    @26
    @0
    @8
    @11
    @17
    w3a
    @3
    @6
    @16
    @12
    @24
    @20
    @22
    w3a
    @65
    @35
    @26
    @8
    @11
    @17
    @57
    @59
    @16
    @17
    @23
    @24
    @7
    @15
    simp31r
    3jca
    @37
    @38
    @51
    @52
    @26
    @24
    @20
    @22
    @7
    @15
    @18
    @23
    @24
    simp33
    @50
    @53
    3jca
    cA
    cP
    cQ
    cS
    cT
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    cdleme22.h
    cdleme22b
    syl232anc
    @26
    cK
    cal
    wcel
    #
    @11
    @33
    @65
    @66
    wb
    @26
    @0
    @67
    @35
    cK
    hlatl
    syl
    #
    @59
    @40
    cA
    @32
    cT
    cK
    c.le
    c.an
    @21
    @63
    @39
    cdleme22.l
    cdleme22.m
    @63
    eqid
    #
    cdleme22.a
    atnle
    syl3anc
    mpbid
    oveq1d
    @26
    @0
    @58
    cT
    @32
    wcel
    #
    @33
    @27
    @21
    c.le
    wbr
    #
    @62
    @47
    wceq
    @35
    @60
    @26
    @11
    @70
    @59
    cA
    @32
    cT
    cK
    @39
    cdleme22.a
    atbase
    syl
    @40
    @26
    @31
    @33
    @34
    @71
    @36
    @40
    @42
    @32
    cK
    c.le
    c.an
    @21
    cW
    @39
    cdleme22.l
    cdleme22.m
    latmle1
    syl3anc
    cA
    @32
    @27
    c.or
    cK
    c.le
    c.an
    cT
    @21
    @39
    cdleme22.l
    cdleme22.j
    cdleme22.m
    cdleme22.a
    atmod4i1
    syl131anc
    @26
    cK
    col
    wcel
    #
    @27
    @32
    wcel
    #
    @64
    @27
    wceq
    @26
    @0
    @72
    @35
    cK
    hlol
    syl
    @26
    @31
    @33
    @34
    @73
    @36
    @40
    @42
    @32
    cK
    c.an
    @21
    cW
    @39
    cdleme22.m
    latmcl
    syl3anc
    @32
    c.or
    cK
    @27
    @63
    @39
    cdleme22.j
    @69
    olj02
    syl2anc
    3eqtr3d
    adantr
    breqtrd
    @26
    @44
    @45
    wb
    #
    @29
    @26
    @67
    @8
    @58
    @74
    @68
    @57
    @60
    cA
    cS
    @27
    cK
    c.le
    cdleme22.l
    cdleme22.a
    atcmp
    syl3anc
    adantr
    mpbid
    eqcomd
    ex
    necon3ad
    mpd
end
