include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cv.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp22.mm"
include "simp21l.mm"
include "simp21r.mm"
include "jca.mm"
include "simp23.mm"
include "simp32.mm"
include "cdlemg31d.mm"
include "syl133anc.mm"
include "simp31.mm"
include "nbrne2.mm"
include "necomd.mm"
include "syl2anc.mm"
include "simp33.mm"
include "4atex3.mm"
include "df-3an.mm"
include "wi.mm"
include "simpl.mm"
include "a1i.mm"
include "simp12l.mm"
include "simp13l.mm"
include "cdlemg31a.mm"
include "syl122anc.mm"
include "simp11l.mm"
include "hlatlej2.mm"
include "syl3anc.mm"
include "clat.mm"
include "cbs.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "adantr.mm"
include "adantl.mm"
include "lattr.mm"
include "mpan2d.mm"
include "anim12d.mm"
include "syl5bi.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"

theorem cdlemg33b0
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let vr: setvar r
  let cG: class G
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg31.n: |- N = ( ( P .\/ v ) ./\ ( Q .\/ ( R ` F ) ) )

  disjoint A r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  disjoint F r
  disjoint A z
  disjoint F z
  disjoint r z
  disjoint H r
  disjoint H z
  disjoint .\/ z
  disjoint K r
  disjoint K z
  disjoint .<_ z
  disjoint N r
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint R z
  disjoint T z
  disjoint W z
  disjoint v z
  disjoint r v
  disjoint G r
  disjoint S r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ N e. A /\ F e. T ) /\ ( P =/= Q /\ v =/= ( R ` F ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( z =/= N /\ z .<_ ( P .\/ v ) ) ) )

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
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    vv
    cv
    #
    cA
    wcel
    #
    @10
    cW
    c.le
    wbr
    #
    wa
    #
    cN
    cA
    wcel
    #
    cF
    cT
    wcel
    #
    w3a
    #
    cP
    cQ
    wne
    #
    @10
    cF
    cR
    cfv
    wne
    #
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @19
    c.or
    co
    cQ
    @19
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    #
    w3a
    #
    w3a
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @23
    cN
    wne
    #
    @23
    @10
    wne
    #
    @23
    cN
    @10
    c.or
    co
    #
    c.le
    wbr
    #
    w3a
    #
    wa
    #
    vz
    cA
    wrex
    #
    @24
    @25
    @23
    cP
    @10
    c.or
    co
    #
    c.le
    wbr
    #
    wa
    #
    wa
    #
    vz
    cA
    wrex
    @22
    @2
    @5
    @8
    @14
    cN
    cW
    c.le
    wbr
    wn
    #
    wa
    @17
    @11
    cN
    @10
    wne
    #
    wa
    @20
    @31
    @2
    @5
    @8
    @16
    @21
    simp11
    #
    @2
    @5
    @8
    @16
    @21
    simp12
    #
    @2
    @5
    @8
    @16
    @21
    simp13
    #
    @22
    @14
    @36
    @9
    @13
    @14
    @15
    @21
    simp22
    #
    @22
    @2
    @5
    @8
    @13
    @15
    @18
    @14
    @36
    @38
    @39
    @40
    @22
    @11
    @12
    @11
    @12
    @14
    @15
    @9
    @21
    simp21l
    #
    @11
    @12
    @14
    @15
    @9
    @21
    simp21r
    #
    jca
    @9
    @13
    @14
    @15
    @21
    simp23
    #
    @9
    @16
    @17
    @18
    @20
    simp32
    @41
    vv
    cA
    cP
    cQ
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg31d
    syl133anc
    #
    jca
    @9
    @16
    @17
    @18
    @20
    simp31
    @22
    @11
    @37
    @42
    @22
    @12
    @36
    @37
    @43
    @45
    @12
    @36
    wa
    @10
    cN
    @10
    cN
    cW
    c.le
    nbrne2
    necomd
    syl2anc
    jca
    @9
    @16
    @17
    @18
    @20
    simp33
    vz
    cA
    cP
    cQ
    cN
    @10
    cH
    c.or
    cK
    c.le
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    cdlemg12.h
    4atex3
    syl133anc
    @22
    @30
    @35
    vz
    cA
    @22
    @23
    cA
    wcel
    #
    wa
    #
    @29
    @34
    @24
    @29
    @25
    @26
    wa
    #
    @28
    wa
    @47
    @34
    @25
    @26
    @28
    df-3an
    @47
    @48
    @25
    @28
    @33
    @48
    @25
    wi
    @47
    @25
    @26
    simpl
    a1i
    @47
    @28
    @27
    @32
    c.le
    wbr
    #
    @33
    @22
    @49
    @46
    @22
    cN
    @32
    c.le
    wbr
    #
    @10
    @32
    c.le
    wbr
    #
    @49
    @22
    @2
    @3
    @6
    @11
    @15
    @50
    @38
    @3
    @4
    @2
    @8
    @16
    @21
    simp12l
    #
    @6
    @7
    @2
    @5
    @16
    @21
    simp13l
    @42
    @44
    vv
    cA
    cP
    cQ
    cR
    cT
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg31.n
    cdlemg31a
    syl122anc
    @22
    @0
    @3
    @11
    @51
    @0
    @1
    @5
    @8
    @16
    @21
    simp11l
    #
    @52
    @42
    cA
    cP
    @10
    c.or
    cK
    c.le
    cdlemg12.l
    cdlemg12.j
    cdlemg12.a
    hlatlej2
    syl3anc
    @22
    cK
    clat
    wcel
    #
    cN
    cK
    cbs
    cfv
    #
    wcel
    #
    @10
    @55
    wcel
    #
    @32
    @55
    wcel
    #
    @50
    @51
    wa
    @49
    wb
    @22
    @0
    @54
    @53
    cK
    hllat
    syl
    #
    @22
    @14
    @56
    @41
    cA
    @55
    cN
    cK
    @55
    eqid
    #
    cdlemg12.a
    atbase
    syl
    @22
    @11
    @57
    @42
    cA
    @55
    @10
    cK
    @60
    cdlemg12.a
    atbase
    syl
    @22
    @0
    @3
    @11
    @58
    @53
    @52
    @42
    cA
    @55
    c.or
    cK
    cP
    @10
    @60
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @55
    c.or
    cK
    c.le
    cN
    @10
    @32
    @60
    cdlemg12.l
    cdlemg12.j
    latjle12
    syl13anc
    mpbi2and
    adantr
    @47
    @54
    @23
    @55
    wcel
    #
    @27
    @55
    wcel
    #
    @58
    @28
    @49
    wa
    @33
    wi
    @22
    @54
    @46
    @59
    adantr
    @46
    @62
    @22
    cA
    @55
    @23
    cK
    @60
    cdlemg12.a
    atbase
    adantl
    @22
    @63
    @46
    @22
    @0
    @14
    @11
    @63
    @53
    @41
    @42
    cA
    @55
    c.or
    cK
    cN
    @10
    @60
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    adantr
    @22
    @58
    @46
    @61
    adantr
    @55
    cK
    c.le
    @23
    @27
    @32
    @60
    cdlemg12.l
    lattr
    syl13anc
    mpan2d
    anim12d
    syl5bi
    anim2d
    reximdva
    mpd
end
