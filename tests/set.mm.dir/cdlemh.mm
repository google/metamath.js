include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "cp0.mm"
include "ccnv.mm"
include "ccom.mm"
include "wceq.mm"
include "simp1.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp23.mm"
include "simp33.mm"
include "cdlemh1.mm"
include "syl122anc.mm"
include "oveq1.mm"
include "col.mm"
include "simp11l.mm"
include "hlol.mm"
include "syl.mm"
include "simp11r.mm"
include "jca.mm"
include "simp13.mm"
include "simp12.mm"
include "ltrncnv.mm"
include "syl2anc.mm"
include "necomd.mm"
include "trlcnv.mm"
include "neeqtrrd.mm"
include "trlcoat.mm"
include "syl3anc.mm"
include "atbase.mm"
include "eqid.mm"
include "olj02.mm"
include "sylan9eqr.mm"
include "clln.mm"
include "ltrnco.mm"
include "trlle.mm"
include "simp22r.mm"
include "nbrne2.mm"
include "llni2.mm"
include "syl31anc.mm"
include "llnneat.mm"
include "nelne2.mm"
include "adantr.mm"
include "eqnetrd.mm"
include "ex.mm"
include "necon2d.mm"
include "mpd.mm"
include "wo.mm"
include "simp32.mm"
include "trlnidat.mm"
include "hlatlej2.mm"
include "simp22.mm"
include "simp31.mm"
include "ltrncnvnid.mm"
include "trlcone.mm"
include "lhp2atnle.mm"
include "syl322anc.mm"
include "nbrne1.mm"
include "2atmat0.mm"
include "syl33anc.mm"
include "eleq1i.mm"
include "eqeq1i.mm"
include "orbi12i.mm"
include "sylibr.mm"
include "ord.mm"
include "necon1ad.mm"
include "simp21.mm"
include "cdlemh2.mm"
include "syld3an2.mm"
include "wb.mm"
include "lhpmatb.mm"
include "syl21anc.mm"
include "mpbird.mm"

theorem cdlemh
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  assume cdlemh.b: |- B = ( Base ` K )
  assume cdlemh.l: |- .<_ = ( le ` K )
  assume cdlemh.j: |- .\/ = ( join ` K )
  assume cdlemh.m: |- ./\ = ( meet ` K )
  assume cdlemh.a: |- A = ( Atoms ` K )
  assume cdlemh.h: |- H = ( LHyp ` K )
  assume cdlemh.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemh.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemh.s: |- S = ( ( P .\/ ( R ` G ) ) ./\ ( Q .\/ ( R ` ( G o. `' F ) ) ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ G e. T ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ Q .<_ ( P .\/ ( R ` F ) ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ ( R ` F ) =/= ( R ` G ) ) ) -> ( S e. A /\ -. S .<_ W ) )

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
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    w3a
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
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cQ
    cP
    cF
    cR
    cfv
    #
    c.or
    co
    c.le
    wbr
    #
    w3a
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cG
    @15
    wne
    #
    @12
    cG
    cR
    cfv
    #
    wne
    #
    w3a
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
    @21
    cS
    cK
    cp0
    cfv
    #
    wne
    #
    @22
    @21
    cS
    cG
    cF
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    cQ
    @28
    c.or
    co
    #
    wceq
    #
    @25
    @21
    @5
    @6
    @9
    @13
    @19
    @31
    @5
    @14
    @20
    simp1
    @6
    @7
    @11
    @13
    @5
    @20
    simp21l
    #
    @9
    @10
    @8
    @13
    @5
    @20
    simp22l
    #
    @5
    @8
    @11
    @13
    @20
    simp23
    @5
    @14
    @16
    @17
    @19
    simp33
    #
    cA
    cB
    cP
    cQ
    cR
    cS
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemh.b
    cdlemh.l
    cdlemh.j
    cdlemh.m
    cdlemh.a
    cdlemh.h
    cdlemh.t
    cdlemh.r
    cdlemh.s
    cdlemh1
    syl122anc
    @21
    cS
    @24
    @29
    @30
    @21
    cS
    @24
    wceq
    #
    @29
    @30
    wne
    @21
    @35
    wa
    @29
    @28
    @30
    @35
    @21
    @29
    @24
    @28
    c.or
    co
    #
    @28
    cS
    @24
    @28
    c.or
    oveq1
    @21
    cK
    col
    wcel
    #
    @28
    cB
    wcel
    #
    @36
    @28
    wceq
    @21
    @0
    @37
    @0
    @1
    @3
    @4
    @14
    @20
    simp11l
    #
    cK
    hlol
    syl
    @21
    @28
    cA
    wcel
    #
    @38
    @21
    @2
    @4
    @26
    cT
    wcel
    #
    wa
    #
    @18
    @26
    cR
    cfv
    #
    wne
    #
    @40
    @21
    @0
    @1
    @39
    @0
    @1
    @3
    @4
    @14
    @20
    simp11r
    #
    jca
    #
    @21
    @4
    @41
    @2
    @3
    @4
    @14
    @20
    simp13
    #
    @21
    @2
    @3
    @41
    @46
    @2
    @3
    @4
    @14
    @20
    simp12
    #
    cT
    cF
    cH
    cK
    cW
    cdlemh.h
    cdlemh.t
    ltrncnv
    syl2anc
    #
    jca
    @21
    @18
    @12
    @43
    @21
    @12
    @18
    @34
    necomd
    @21
    @2
    @3
    @43
    @12
    wceq
    @46
    @48
    cR
    cT
    cF
    cH
    cK
    cW
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcnv
    syl2anc
    neeqtrrd
    #
    cA
    cR
    cT
    cG
    @26
    cH
    cK
    cW
    cdlemh.a
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcoat
    syl3anc
    #
    cA
    cB
    @28
    cK
    cdlemh.b
    cdlemh.a
    atbase
    syl
    cB
    c.or
    cK
    @28
    @24
    cdlemh.b
    cdlemh.j
    @24
    eqid
    #
    olj02
    syl2anc
    sylan9eqr
    @21
    @28
    @30
    wne
    #
    @35
    @21
    @40
    @30
    cA
    wcel
    wn
    #
    @53
    @51
    @21
    @0
    @30
    cK
    clln
    cfv
    #
    wcel
    #
    @54
    @39
    @21
    @0
    @9
    @40
    cQ
    @28
    wne
    #
    @56
    @39
    @33
    @51
    @21
    @28
    cW
    c.le
    wbr
    #
    @10
    @57
    @21
    @2
    @27
    cT
    wcel
    #
    @58
    @46
    @21
    @2
    @4
    @41
    @59
    @46
    @47
    @49
    cT
    cG
    @26
    cH
    cK
    cW
    cdlemh.h
    cdlemh.t
    ltrnco
    syl3anc
    cR
    cT
    @27
    cH
    cK
    c.le
    cW
    cdlemh.l
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlle
    syl2anc
    #
    @9
    @10
    @8
    @13
    @5
    @20
    simp22r
    @58
    @10
    wa
    @28
    cQ
    @28
    cQ
    cW
    c.le
    nbrne2
    necomd
    syl2anc
    cA
    cQ
    @28
    c.or
    cK
    @55
    cdlemh.j
    cdlemh.a
    @55
    eqid
    #
    llni2
    syl31anc
    cA
    cK
    @55
    @30
    cdlemh.a
    @61
    llnneat
    syl2anc
    @28
    @30
    cA
    nelne2
    syl2anc
    adantr
    eqnetrd
    ex
    necon2d
    mpd
    @21
    @22
    cS
    @24
    @21
    @22
    @35
    @21
    cP
    @18
    c.or
    co
    #
    @30
    c.an
    co
    #
    cA
    wcel
    #
    @63
    @24
    wceq
    #
    wo
    #
    @22
    @35
    wo
    @21
    @0
    @6
    @18
    cA
    wcel
    #
    @9
    @40
    @62
    @30
    wne
    #
    @66
    @39
    @32
    @21
    @2
    @4
    @17
    @67
    @46
    @47
    @5
    @14
    @16
    @17
    @19
    simp32
    cA
    cB
    cR
    cT
    cG
    cH
    cK
    cW
    cdlemh.b
    cdlemh.a
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlnidat
    syl3anc
    #
    @33
    @51
    @21
    @18
    @62
    c.le
    wbr
    #
    @18
    @30
    c.le
    wbr
    wn
    #
    @68
    @21
    @0
    @6
    @67
    @70
    @39
    @32
    @69
    cA
    cP
    @18
    c.or
    cK
    c.le
    cdlemh.l
    cdlemh.j
    cdlemh.a
    hlatlej2
    syl3anc
    @21
    @2
    @11
    @28
    @18
    wne
    #
    @40
    @58
    @67
    @18
    cW
    c.le
    wbr
    #
    @71
    @46
    @5
    @8
    @11
    @13
    @20
    simp22
    #
    @21
    @2
    @4
    @41
    @44
    @26
    @15
    wne
    #
    @72
    @46
    @47
    @49
    @50
    @21
    @2
    @3
    @16
    @75
    @46
    @48
    @5
    @14
    @16
    @17
    @19
    simp31
    cB
    cT
    cF
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    cdlemh.t
    ltrncnvnid
    syl3anc
    @2
    @42
    @44
    @75
    wa
    w3a
    @18
    @28
    cB
    cR
    cT
    cG
    @26
    cH
    cK
    cW
    cdlemh.b
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlcone
    necomd
    syl122anc
    @51
    @60
    @69
    @21
    @2
    @4
    @73
    @46
    @47
    cR
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemh.l
    cdlemh.h
    cdlemh.t
    cdlemh.r
    trlle
    syl2anc
    cA
    cQ
    @28
    cH
    c.or
    cK
    c.le
    @18
    cW
    cdlemh.l
    cdlemh.j
    cdlemh.a
    cdlemh.h
    lhp2atnle
    syl322anc
    @18
    @62
    @30
    c.le
    nbrne1
    syl2anc
    cA
    cP
    @18
    cQ
    @28
    c.or
    cK
    c.an
    @24
    cdlemh.j
    cdlemh.m
    @52
    cdlemh.a
    2atmat0
    syl33anc
    @22
    @64
    @35
    @65
    cS
    @63
    cA
    cdlemh.s
    eleq1i
    cS
    @63
    @24
    cdlemh.s
    eqeq1i
    orbi12i
    sylibr
    ord
    necon1ad
    mpd
    #
    @21
    @23
    cS
    cW
    c.an
    co
    @24
    wceq
    #
    @5
    @8
    @11
    wa
    @14
    @20
    @77
    @21
    @8
    @11
    @5
    @8
    @11
    @13
    @20
    simp21
    @74
    jca
    cA
    cB
    cP
    cQ
    cR
    cS
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    @24
    cdlemh.b
    cdlemh.l
    cdlemh.j
    cdlemh.m
    cdlemh.a
    cdlemh.h
    cdlemh.t
    cdlemh.r
    cdlemh.s
    @52
    cdlemh2
    syld3an2
    @21
    @0
    @1
    @22
    @23
    @77
    wb
    @39
    @45
    @76
    cA
    cS
    cH
    cK
    c.le
    c.an
    cW
    @24
    cdlemh.l
    cdlemh.m
    @52
    cdlemh.a
    cdlemh.h
    lhpmatb
    syl21anc
    mpbird
    jca
end
