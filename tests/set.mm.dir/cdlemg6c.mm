include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "simpl1.mm"
include "simprl.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl31.mm"
include "simprr.mm"
include "cbs.mm"
include "wi.mm"
include "simpl1l.mm"
include "simp22l.mm"
include "adantr.mm"
include "simprll.mm"
include "eqid.mm"
include "trlcl.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "simp22r.mm"
include "trlle.mm"
include "syl5eqbr.mm"
include "clat.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "simp1r.mm"
include "lhpbase.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpan2d.mm"
include "mtod.mm"
include "hlexch2.mm"
include "syl131anc.mm"
include "simpl32.mm"
include "simp21l.mm"
include "latlej2.mm"
include "syl3anc.mm"
include "wb.mm"
include "latjcl.mm"
include "latjle12.mm"
include "mpbi2and.mm"
include "syld.mm"
include "simpl21.mm"
include "simpl33.mm"
include "cdlemg6a.mm"
include "syl133anc.mm"
include "cdlemg6b.mm"
include "ex.mm"

theorem cdlemg6c
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
  let cV: class V
  let cW: class W
  let vr: setvar r
  assume cdlemg4.l: |- .<_ = ( le ` K )
  assume cdlemg4.a: |- A = ( Atoms ` K )
  assume cdlemg4.h: |- H = ( LHyp ` K )
  assume cdlemg4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemg4.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemg4.j: |- .\/ = ( join ` K )
  assume cdlemg4b.v: |- V = ( R ` G )

  disjoint A r
  disjoint F r
  disjoint G r
  disjoint H r
  disjoint .\/ r
  disjoint K r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint T r
  disjoint V r
  disjoint W r
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) /\ F e. T ) /\ ( G e. T /\ Q .<_ ( P .\/ V ) /\ ( F ` ( G ` P ) ) = P ) ) -> ( ( ( r e. A /\ -. r .<_ W ) /\ -. r .<_ ( P .\/ V ) ) -> ( F ` ( G ` Q ) ) = Q ) )

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
    #
    wn
    #
    wa
    #
    cF
    cT
    wcel
    #
    w3a
    #
    cG
    cT
    wcel
    #
    cQ
    cP
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    cP
    cG
    cfv
    cF
    cfv
    cP
    wceq
    #
    w3a
    #
    w3a
    #
    vr
    cv
    #
    cA
    wcel
    #
    @18
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @18
    @13
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cQ
    cG
    cfv
    cF
    cfv
    cQ
    wceq
    #
    @17
    @24
    wa
    #
    @2
    @21
    @9
    @10
    @12
    cQ
    @18
    cV
    c.or
    co
    c.le
    wbr
    #
    wn
    @18
    cG
    cfv
    cF
    cfv
    @18
    wceq
    #
    @25
    @2
    @11
    @16
    @24
    simpl1
    #
    @17
    @21
    @23
    simprl
    #
    @5
    @9
    @10
    @2
    @16
    @24
    simpl22
    @5
    @9
    @10
    @2
    @16
    @24
    simpl23
    #
    @12
    @14
    @15
    @2
    @11
    @24
    simpl31
    #
    @26
    @27
    @22
    @17
    @21
    @23
    simprr
    #
    @26
    @27
    @18
    cQ
    cV
    c.or
    co
    #
    c.le
    wbr
    #
    @22
    @26
    @0
    @6
    @19
    cV
    cK
    cbs
    cfv
    #
    wcel
    #
    cQ
    cV
    c.le
    wbr
    #
    wn
    @27
    @35
    wi
    @0
    @1
    @11
    @16
    @24
    simpl1l
    @17
    @6
    @24
    @6
    @8
    @5
    @10
    @2
    @16
    simp22l
    #
    adantr
    @17
    @19
    @20
    @23
    simprll
    #
    @26
    cV
    cG
    cR
    cfv
    #
    @36
    cdlemg4b.v
    @26
    @2
    @12
    @41
    @36
    wcel
    @29
    @32
    @36
    cR
    cT
    cG
    cH
    cK
    cW
    @36
    eqid
    #
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    trlcl
    syl2anc
    syl5eqel
    #
    @26
    @38
    @7
    @17
    @8
    @24
    @6
    @8
    @5
    @10
    @2
    @16
    simp22r
    adantr
    @26
    @38
    cV
    cW
    c.le
    wbr
    #
    @7
    @26
    cV
    @41
    cW
    c.le
    cdlemg4b.v
    @26
    @2
    @12
    @41
    cW
    c.le
    wbr
    @29
    @32
    cR
    cT
    cG
    cH
    cK
    c.le
    cW
    cdlemg4.l
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    trlle
    syl2anc
    syl5eqbr
    @26
    cK
    clat
    wcel
    #
    cQ
    @36
    wcel
    #
    @37
    cW
    @36
    wcel
    #
    @38
    @44
    wa
    @7
    wi
    @17
    @45
    @24
    @17
    @0
    @45
    @0
    @1
    @11
    @16
    simp1l
    cK
    hllat
    syl
    adantr
    #
    @17
    @46
    @24
    @17
    @6
    @46
    @39
    cA
    @36
    cQ
    cK
    @42
    cdlemg4.a
    atbase
    syl
    adantr
    #
    @43
    @17
    @47
    @24
    @17
    @1
    @47
    @0
    @1
    @11
    @16
    simp1r
    @36
    cH
    cK
    cW
    @42
    cdlemg4.h
    lhpbase
    syl
    adantr
    @36
    cK
    c.le
    cQ
    cV
    cW
    @42
    cdlemg4.l
    lattr
    syl13anc
    mpan2d
    mtod
    cA
    @36
    cQ
    @18
    c.or
    cK
    c.le
    cV
    @42
    cdlemg4.l
    cdlemg4.j
    cdlemg4.a
    hlexch2
    syl131anc
    @26
    @35
    @34
    @13
    c.le
    wbr
    #
    @22
    @26
    @14
    cV
    @13
    c.le
    wbr
    #
    @50
    @12
    @14
    @15
    @2
    @11
    @24
    simpl32
    @26
    @45
    cP
    @36
    wcel
    #
    @37
    @51
    @48
    @26
    @3
    @52
    @17
    @3
    @24
    @3
    @4
    @9
    @10
    @2
    @16
    simp21l
    adantr
    cA
    @36
    cP
    cK
    @42
    cdlemg4.a
    atbase
    syl
    #
    @43
    @36
    c.or
    cK
    c.le
    cP
    cV
    @42
    cdlemg4.l
    cdlemg4.j
    latlej2
    syl3anc
    @26
    @45
    @46
    @37
    @13
    @36
    wcel
    #
    @14
    @51
    wa
    @50
    wb
    @48
    @49
    @43
    @26
    @45
    @52
    @37
    @54
    @48
    @53
    @43
    @36
    c.or
    cK
    cP
    cV
    @42
    cdlemg4.j
    latjcl
    syl3anc
    #
    @36
    c.or
    cK
    c.le
    cQ
    cV
    @13
    @42
    cdlemg4.l
    cdlemg4.j
    latjle12
    syl13anc
    mpbi2and
    @26
    @45
    @18
    @36
    wcel
    #
    @34
    @36
    wcel
    #
    @54
    @35
    @50
    wa
    @22
    wi
    @48
    @26
    @19
    @56
    @40
    cA
    @36
    @18
    cK
    @42
    cdlemg4.a
    atbase
    syl
    @26
    @45
    @46
    @37
    @57
    @48
    @49
    @43
    @36
    c.or
    cK
    cQ
    cV
    @42
    cdlemg4.j
    latjcl
    syl3anc
    @55
    @36
    cK
    c.le
    @18
    @34
    @13
    @42
    cdlemg4.l
    lattr
    syl13anc
    mpan2d
    syld
    mtod
    @26
    @2
    @5
    @21
    @10
    @12
    @23
    @15
    @28
    @29
    @5
    @9
    @10
    @2
    @16
    @24
    simpl21
    @30
    @31
    @32
    @33
    @12
    @14
    @15
    @2
    @11
    @24
    simpl33
    cA
    cP
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cV
    cW
    vr
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg6a
    syl133anc
    cA
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    cV
    cW
    vr
    cdlemg4.l
    cdlemg4.a
    cdlemg4.h
    cdlemg4.t
    cdlemg4.r
    cdlemg4.j
    cdlemg4b.v
    cdlemg6b
    syl133anc
    ex
end
