include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "co.mm"
include "simp11l.mm"
include "simp22l.mm"
include "simp11.mm"
include "simp13.mm"
include "simp32.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "hlatlej1.mm"
include "cdlemkole.mm"
include "clat.mm"
include "wb.mm"
include "hllat.mm"
include "syl.mm"
include "atbase.mm"
include "cdlemkoatnle.mm"
include "simpld.mm"
include "hlatjcl.mm"
include "latjle12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "simp22.mm"
include "trljat3.mm"
include "breqtrd.mm"

theorem cdlemk1u
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  assume cdlemk1.b: |- B = ( Base ` K )
  assume cdlemk1.l: |- .<_ = ( le ` K )
  assume cdlemk1.j: |- .\/ = ( join ` K )
  assume cdlemk1.m: |- ./\ = ( meet ` K )
  assume cdlemk1.a: |- A = ( Atoms ` K )
  assume cdlemk1.h: |- H = ( LHyp ` K )
  assume cdlemk1.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk1.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk1.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk1.o: |- O = ( S ` D )

  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint D f
  disjoint D i
  disjoint F f
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P f
  disjoint P i
  disjoint R f
  disjoint R i
  disjoint T f
  disjoint T i
  disjoint W f
  disjoint W i
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ ( R ` D ) =/= ( R ` F ) ) ) -> ( P .\/ ( O ` P ) ) .<_ ( ( D ` P ) .\/ ( R ` D ) ) )

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
    cD
    cT
    wcel
    #
    w3a
    #
    cN
    cT
    wcel
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
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
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
    cD
    @13
    wne
    #
    cD
    cR
    cfv
    #
    @10
    wne
    #
    w3a
    #
    w3a
    #
    cP
    cP
    cO
    cfv
    #
    c.or
    co
    #
    cP
    @16
    c.or
    co
    #
    cP
    cD
    cfv
    @16
    c.or
    co
    #
    c.le
    @19
    cP
    @22
    c.le
    wbr
    #
    @20
    @22
    c.le
    wbr
    #
    @21
    @22
    c.le
    wbr
    #
    @19
    @0
    @7
    @16
    cA
    wcel
    #
    @24
    @0
    @1
    @3
    @4
    @12
    @18
    simp11l
    #
    @7
    @8
    @6
    @11
    @5
    @18
    simp22l
    #
    @19
    @2
    @4
    @15
    @27
    @2
    @3
    @4
    @12
    @18
    simp11
    #
    @2
    @3
    @4
    @12
    @18
    simp13
    #
    @5
    @12
    @14
    @15
    @17
    simp32
    cA
    cB
    cR
    cT
    cD
    cH
    cK
    cW
    cdlemk1.b
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlnidat
    syl3anc
    #
    cA
    cP
    @16
    c.or
    cK
    c.le
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    hlatlej1
    syl3anc
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.s
    cdlemk1.o
    cdlemkole
    @19
    cK
    clat
    wcel
    #
    cP
    cB
    wcel
    #
    @20
    cB
    wcel
    #
    @22
    cB
    wcel
    #
    @24
    @25
    wa
    @26
    wb
    @19
    @0
    @33
    @28
    cK
    hllat
    syl
    @19
    @7
    @34
    @29
    cA
    cB
    cP
    cK
    cdlemk1.b
    cdlemk1.a
    atbase
    syl
    @19
    @20
    cA
    wcel
    #
    @35
    @19
    @37
    @20
    cW
    c.le
    wbr
    wn
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.s
    cdlemk1.o
    cdlemkoatnle
    simpld
    cA
    cB
    @20
    cK
    cdlemk1.b
    cdlemk1.a
    atbase
    syl
    @19
    @0
    @7
    @27
    @36
    @28
    @29
    @32
    cA
    cB
    c.or
    cK
    cP
    @16
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    cB
    c.or
    cK
    c.le
    cP
    @20
    @22
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    latjle12
    syl13anc
    mpbi2and
    @19
    @2
    @4
    @9
    @22
    @23
    wceq
    @30
    @31
    @5
    @6
    @9
    @11
    @18
    simp22
    cA
    cP
    cR
    cT
    cD
    cH
    c.or
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trljat3
    syl3anc
    breqtrd
end
