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
include "simp22l.mm"
include "simp21.mm"
include "simp23l.mm"
include "simp32.mm"
include "cdlemg31d.mm"
include "syl133anc.mm"
include "jca.mm"
include "simp31l.mm"
include "simp22r.mm"
include "simp31r.mm"
include "simp33.mm"
include "4atex3.mm"
include "idd.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp21l.mm"
include "cdlemg31a.mm"
include "syl122anc.mm"
include "simp23r.mm"
include "clat.mm"
include "cbs.mm"
include "wi.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "eqid.mm"
include "atbase.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "latjlej12.mm"
include "mp2and.mm"
include "latjidm.mm"
include "syl2anc.mm"
include "breqtrd.mm"
include "adantr.mm"
include "adantl.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpan2d.mm"
include "3anim123d.mm"
include "anim2d.mm"
include "reximdva.mm"
include "mpd.mm"

theorem cdlemg33a
  let vz: setvar z
  let vv: setvar v
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let vr: setvar r
  let cS: class S
  assume cdlemg12.l: |- .<_ = ( le ` K )
  assume cdlemg12.j: |- .\/ = ( join ` K )
  assume cdlemg12.m: |- ./\ = ( meet ` K )
  assume cdlemg12.a: |- A = ( Atoms ` K )
  assume cdlemg12.h: |- H = ( LHyp ` K )
  assume cdlemg12.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg12b.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg31.n: |- N = ( ( P .\/ v ) ./\ ( Q .\/ ( R ` F ) ) )
  assume cdlemg33.o: |- O = ( ( P .\/ v ) ./\ ( Q .\/ ( R ` G ) ) )

  disjoint A r
  disjoint G r
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
  disjoint G z
  disjoint O z
  disjoint O r
  disjoint S r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( v e. A /\ v .<_ W ) /\ ( N e. A /\ O e. A ) /\ ( F e. T /\ G e. T ) ) /\ ( ( P =/= Q /\ N =/= O ) /\ v =/= ( R ` F ) /\ E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> E. z e. A ( -. z .<_ W /\ ( z =/= N /\ z =/= O /\ z .<_ ( P .\/ v ) ) ) )

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
    cO
    cA
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
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cN
    cO
    wne
    #
    wa
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
    @25
    c.or
    co
    cQ
    @25
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
    @29
    cN
    wne
    #
    @29
    cO
    wne
    #
    @29
    cN
    cO
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
    @30
    @31
    @32
    @29
    cP
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
    @28
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
    @21
    @15
    @22
    wa
    @26
    @37
    @2
    @5
    @8
    @20
    @27
    simp11
    #
    @2
    @5
    @8
    @20
    @27
    simp12
    #
    @2
    @5
    @8
    @20
    @27
    simp13
    #
    @28
    @14
    @42
    @14
    @15
    @13
    @19
    @9
    @27
    simp22l
    #
    @28
    @2
    @5
    @8
    @13
    @17
    @24
    @14
    @42
    @43
    @44
    @45
    @9
    @13
    @16
    @19
    @27
    simp21
    @17
    @18
    @13
    @16
    @9
    @27
    simp23l
    #
    @9
    @20
    @23
    @24
    @26
    simp32
    @46
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
    jca
    @21
    @22
    @24
    @26
    @9
    @20
    simp31l
    @28
    @15
    @22
    @14
    @15
    @13
    @19
    @9
    @27
    simp22r
    #
    @21
    @22
    @24
    @26
    @9
    @20
    simp31r
    jca
    @9
    @20
    @23
    @24
    @26
    simp33
    vz
    cA
    cP
    cQ
    cN
    cO
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
    @28
    @36
    @41
    vz
    cA
    @28
    @29
    cA
    wcel
    #
    wa
    #
    @35
    @40
    @30
    @50
    @31
    @31
    @32
    @32
    @34
    @39
    @50
    @31
    idd
    @50
    @32
    idd
    @50
    @34
    @33
    @38
    c.le
    wbr
    #
    @39
    @28
    @51
    @49
    @28
    @33
    @38
    @38
    c.or
    co
    #
    @38
    c.le
    @28
    cN
    @38
    c.le
    wbr
    #
    cO
    @38
    c.le
    wbr
    #
    @33
    @52
    c.le
    wbr
    #
    @28
    @2
    @3
    @6
    @11
    @17
    @53
    @43
    @3
    @4
    @2
    @8
    @20
    @27
    simp12l
    #
    @6
    @7
    @2
    @5
    @20
    @27
    simp13l
    #
    @11
    @12
    @16
    @19
    @9
    @27
    simp21l
    #
    @47
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
    @28
    @2
    @3
    @6
    @11
    @18
    @54
    @43
    @56
    @57
    @58
    @17
    @18
    @13
    @16
    @9
    @27
    simp23r
    vv
    cA
    cP
    cQ
    cR
    cT
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cO
    cW
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg33.o
    cdlemg31a
    syl122anc
    @28
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
    @38
    @60
    wcel
    #
    cO
    @60
    wcel
    #
    @62
    @53
    @54
    wa
    @55
    wi
    @28
    @0
    @59
    @0
    @1
    @5
    @8
    @20
    @27
    simp11l
    #
    cK
    hllat
    syl
    #
    @28
    @14
    @61
    @46
    cA
    @60
    cN
    cK
    @60
    eqid
    #
    cdlemg12.a
    atbase
    syl
    @28
    @0
    @3
    @11
    @62
    @64
    @56
    @58
    cA
    @60
    c.or
    cK
    cP
    @10
    @66
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @28
    @15
    @63
    @48
    cA
    @60
    cO
    cK
    @66
    cdlemg12.a
    atbase
    syl
    @67
    @60
    c.or
    cK
    c.le
    @38
    cN
    @38
    cO
    @66
    cdlemg12.l
    cdlemg12.j
    latjlej12
    syl122anc
    mp2and
    @28
    @59
    @62
    @52
    @38
    wceq
    @65
    @67
    @60
    c.or
    cK
    @38
    @66
    cdlemg12.j
    latjidm
    syl2anc
    breqtrd
    adantr
    @50
    @59
    @29
    @60
    wcel
    #
    @33
    @60
    wcel
    #
    @62
    @34
    @51
    wa
    @39
    wi
    @28
    @59
    @49
    @65
    adantr
    @49
    @68
    @28
    cA
    @60
    @29
    cK
    @66
    cdlemg12.a
    atbase
    adantl
    @28
    @69
    @49
    @28
    @0
    @14
    @15
    @69
    @64
    @46
    @48
    cA
    @60
    c.or
    cK
    cN
    cO
    @66
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    adantr
    @28
    @62
    @49
    @67
    adantr
    @60
    cK
    c.le
    @29
    @33
    @38
    @66
    cdlemg12.l
    lattr
    syl13anc
    mpan2d
    3anim123d
    anim2d
    reximdva
    mpd
end
