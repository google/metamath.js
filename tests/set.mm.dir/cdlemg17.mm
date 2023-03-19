include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "cbs.mm"
include "simp11.mm"
include "simp22.mm"
include "simp12l.mm"
include "eqid.mm"
include "atbase.mm"
include "syl.mm"
include "simp21.mm"
include "ltrncoat.mm"
include "syl121anc.mm"
include "ltrnj.mm"
include "syl112anc.mm"
include "simp1.mm"
include "simp23.mm"
include "simp3.mm"
include "cdlemg17b.mm"
include "fveq2d.mm"
include "cdlemg17jq.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "simp13l.mm"
include "cdlemg17bq.mm"
include "cdlemg17j.mm"
include "simp11l.mm"
include "hlatjcl.mm"
include "syl3anc.mm"
include "ltrnm.mm"
include "clat.mm"
include "hllat.mm"
include "latmcom.mm"
include "3eqtr4d.mm"

theorem cdlemg17
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

  disjoint A r
  disjoint G r
  disjoint .\/ r
  disjoint .<_ r
  disjoint P r
  disjoint Q r
  disjoint W r
  disjoint F r
  disjoint S r
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( F e. T /\ G e. T /\ P =/= Q ) /\ ( ( G ` P ) =/= P /\ ( R ` G ) .<_ ( P .\/ Q ) /\ -. E. r e. A ( -. r .<_ W /\ ( P .\/ r ) = ( Q .\/ r ) ) ) ) -> ( G ` ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ ( Q .\/ ( F ` ( G ` Q ) ) ) ) ) = ( ( P .\/ ( F ` ( G ` P ) ) ) ./\ ( Q .\/ ( F ` ( G ` Q ) ) ) ) )

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
    cF
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    cP
    cQ
    wne
    #
    w3a
    #
    cP
    cG
    cfv
    #
    cP
    wne
    cG
    cR
    cfv
    cP
    cQ
    c.or
    co
    c.le
    wbr
    vr
    cv
    #
    cW
    c.le
    wbr
    wn
    cP
    @15
    c.or
    co
    cQ
    @15
    c.or
    co
    wceq
    wa
    vr
    cA
    wrex
    wn
    w3a
    #
    w3a
    #
    cP
    @14
    cF
    cfv
    #
    c.or
    co
    #
    cG
    cfv
    #
    cQ
    cQ
    cG
    cfv
    #
    cF
    cfv
    #
    c.or
    co
    #
    cG
    cfv
    #
    c.an
    co
    #
    @23
    @19
    c.an
    co
    #
    @19
    @23
    c.an
    co
    #
    cG
    cfv
    #
    @27
    @17
    @20
    @23
    @24
    @19
    c.an
    @17
    @20
    @14
    @18
    cG
    cfv
    #
    c.or
    co
    #
    @23
    @17
    @2
    @11
    cP
    cK
    cbs
    cfv
    #
    wcel
    #
    @18
    @31
    wcel
    #
    @20
    @30
    wceq
    @2
    @5
    @8
    @13
    @16
    simp11
    #
    @9
    @10
    @11
    @12
    @16
    simp22
    #
    @17
    @3
    @32
    @3
    @4
    @2
    @8
    @13
    @16
    simp12l
    #
    cA
    @31
    cP
    cK
    @31
    eqid
    #
    cdlemg12.a
    atbase
    syl
    @17
    @18
    cA
    wcel
    #
    @33
    @17
    @2
    @10
    @11
    @3
    @38
    @34
    @9
    @10
    @11
    @12
    @16
    simp21
    #
    @35
    @36
    cA
    cP
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrncoat
    syl121anc
    #
    cA
    @31
    @18
    cK
    @37
    cdlemg12.a
    atbase
    syl
    @31
    cT
    cG
    cH
    c.or
    cK
    cW
    cP
    @18
    @37
    cdlemg12.j
    cdlemg12.h
    cdlemg12.t
    ltrnj
    syl112anc
    @17
    @14
    cQ
    @29
    @22
    c.or
    @17
    @9
    @11
    @12
    @16
    @14
    cQ
    wceq
    @9
    @13
    @16
    simp1
    @35
    @9
    @10
    @11
    @12
    @16
    simp23
    @9
    @13
    @16
    simp3
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
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17b
    syl121anc
    #
    @17
    @29
    cQ
    cF
    cfv
    #
    cG
    cfv
    @22
    @17
    @18
    @42
    cG
    @17
    @14
    cQ
    cF
    @41
    fveq2d
    fveq2d
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17jq
    eqtrd
    oveq12d
    eqtrd
    @17
    @24
    @21
    @22
    cG
    cfv
    #
    c.or
    co
    #
    @19
    @17
    @2
    @11
    cQ
    @31
    wcel
    #
    @22
    @31
    wcel
    #
    @24
    @44
    wceq
    @34
    @35
    @17
    @6
    @45
    @6
    @7
    @2
    @5
    @13
    @16
    simp13l
    #
    cA
    @31
    cQ
    cK
    @37
    cdlemg12.a
    atbase
    syl
    @17
    @22
    cA
    wcel
    #
    @46
    @17
    @2
    @10
    @11
    @6
    @48
    @34
    @39
    @35
    @47
    cA
    cQ
    cT
    cF
    cG
    cH
    cK
    c.le
    cW
    cdlemg12.l
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    ltrncoat
    syl121anc
    #
    cA
    @31
    @22
    cK
    @37
    cdlemg12.a
    atbase
    syl
    @31
    cT
    cG
    cH
    c.or
    cK
    cW
    cQ
    @22
    @37
    cdlemg12.j
    cdlemg12.h
    cdlemg12.t
    ltrnj
    syl112anc
    @17
    @21
    cP
    @43
    @18
    c.or
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17bq
    #
    @17
    @43
    cP
    cF
    cfv
    #
    cG
    cfv
    @18
    @17
    @22
    @51
    cG
    @17
    @21
    cP
    cF
    @50
    fveq2d
    fveq2d
    cA
    cP
    cQ
    cR
    cT
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vr
    cdlemg12.l
    cdlemg12.j
    cdlemg12.m
    cdlemg12.a
    cdlemg12.h
    cdlemg12.t
    cdlemg12b.r
    cdlemg17j
    eqtrd
    oveq12d
    eqtrd
    oveq12d
    @17
    @2
    @11
    @19
    @31
    wcel
    #
    @23
    @31
    wcel
    #
    @28
    @25
    wceq
    @34
    @35
    @17
    @0
    @3
    @38
    @52
    @0
    @1
    @5
    @8
    @13
    @16
    simp11l
    #
    @36
    @40
    cA
    @31
    c.or
    cK
    cP
    @18
    @37
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @17
    @0
    @6
    @48
    @53
    @54
    @47
    @49
    cA
    @31
    c.or
    cK
    cQ
    @22
    @37
    cdlemg12.j
    cdlemg12.a
    hlatjcl
    syl3anc
    #
    @31
    cT
    cG
    cH
    cK
    c.an
    cW
    @19
    @23
    @37
    cdlemg12.m
    cdlemg12.h
    cdlemg12.t
    ltrnm
    syl112anc
    @17
    cK
    clat
    wcel
    #
    @52
    @53
    @27
    @26
    wceq
    @17
    @0
    @57
    @54
    cK
    hllat
    syl
    @55
    @56
    @31
    cK
    c.an
    @19
    @23
    @37
    cdlemg12.m
    latmcom
    syl3anc
    3eqtr4d
end
