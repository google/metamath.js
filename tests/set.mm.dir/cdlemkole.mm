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
include "ccnv.mm"
include "ccom.mm"
include "cdlemk13.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simp22l.mm"
include "simp11.mm"
include "simp13.mm"
include "simp32.mm"
include "trlnidat.mm"
include "syl3anc.mm"
include "hlatjcl.mm"
include "simp21.mm"
include "ltrnat.mm"
include "simp12.mm"
include "simp33.mm"
include "trlcocnvat.mm"
include "syl121anc.mm"
include "latmle1.mm"
include "eqbrtrd.mm"

theorem cdlemkole
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ ( R ` D ) =/= ( R ` F ) ) ) -> ( O ` P ) .<_ ( P .\/ ( R ` D ) ) )

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
    cO
    cfv
    cP
    @16
    c.or
    co
    #
    cP
    cN
    cfv
    #
    cD
    cF
    ccnv
    ccom
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    @20
    c.le
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
    cdlemk13
    @19
    cK
    clat
    wcel
    #
    @20
    cB
    wcel
    #
    @23
    cB
    wcel
    #
    @24
    @20
    c.le
    wbr
    @19
    @0
    @25
    @0
    @1
    @3
    @4
    @12
    @18
    simp11l
    #
    cK
    hllat
    syl
    @19
    @0
    @7
    @16
    cA
    wcel
    #
    @26
    @28
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
    @29
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
    @19
    @0
    @21
    cA
    wcel
    #
    @22
    cA
    wcel
    #
    @27
    @28
    @19
    @2
    @6
    @7
    @33
    @31
    @5
    @6
    @9
    @11
    @18
    simp21
    @30
    cA
    cP
    cT
    cN
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    ltrnat
    syl3anc
    @19
    @2
    @4
    @3
    @17
    @34
    @31
    @32
    @2
    @3
    @4
    @12
    @18
    simp12
    @5
    @12
    @14
    @15
    @17
    simp33
    cA
    cR
    cT
    cD
    cF
    cH
    cK
    cW
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnvat
    syl121anc
    cA
    cB
    c.or
    cK
    @21
    @22
    cdlemk1.b
    cdlemk1.j
    cdlemk1.a
    hlatjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    @20
    @23
    cdlemk1.b
    cdlemk1.l
    cdlemk1.m
    latmle1
    syl3anc
    eqbrtrd
end
