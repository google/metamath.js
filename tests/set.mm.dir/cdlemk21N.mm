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
include "simp11.mm"
include "simp21r.mm"
include "simp22.mm"
include "trljat1.mm"
include "syl3anc.mm"
include "fveq1i.mm"
include "a1i.mm"
include "simp13.mm"
include "trlcocnv.mm"
include "oveq12d.mm"
include "simp23.mm"
include "simp12.mm"
include "simp21l.mm"
include "simp3r1.mm"
include "simp3r2.mm"
include "necomd.mm"
include "jca.mm"
include "simp3l1.mm"
include "simp3l3.mm"
include "simp3l2.mm"
include "3jca.mm"
include "cdlemkuv2.mm"
include "syl333anc.mm"
include "simp3r3.mm"
include "cdlemk12.mm"
include "3eqtr4rd.mm"

theorem cdlemk21N
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
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
  let cX: class X
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
  assume cdlemk1.u: |- U = ( e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( O ` P ) .\/ ( R ` ( e o. `' D ) ) ) ) ) )

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
  disjoint ./\ e
  disjoint .\/ e
  disjoint D e
  disjoint e j
  disjoint G e
  disjoint G j
  disjoint O e
  disjoint P e
  disjoint R e
  disjoint T e
  disjoint W e
  disjoint ./\ j
  disjoint .<_ j
  disjoint .\/ j
  disjoint A j
  disjoint D j
  disjoint F j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint O j
  disjoint P j
  disjoint R j
  disjoint T j
  disjoint W j
  disjoint F e
  disjoint G i
  disjoint G f
  disjoint X e
  disjoint X j
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( ( N e. T /\ G e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` D ) /\ ( R ` G ) =/= ( R ` F ) ) ) ) -> ( ( S ` G ) ` P ) = ( ( U ` G ) ` P ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cG
    cT
    wcel
    #
    wa
    #
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
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
    @11
    wne
    #
    cG
    @11
    wne
    #
    w3a
    #
    cD
    cR
    cfv
    #
    @8
    wne
    #
    cG
    cR
    cfv
    #
    @16
    wne
    #
    @18
    @8
    wne
    #
    w3a
    #
    wa
    #
    w3a
    #
    cP
    @18
    c.or
    co
    #
    cP
    cO
    cfv
    #
    cG
    cD
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
    cP
    cP
    cG
    cfv
    c.or
    co
    #
    cP
    cD
    cS
    cfv
    #
    cfv
    #
    cD
    cG
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
    cP
    cG
    cU
    cfv
    cfv
    #
    cP
    cG
    cS
    cfv
    cfv
    #
    @23
    @24
    @29
    @27
    @33
    c.an
    @23
    @0
    @5
    @7
    @24
    @29
    wceq
    @0
    @1
    @2
    @10
    @22
    simp11
    #
    @4
    @5
    @7
    @9
    @3
    @22
    simp21r
    #
    @3
    @6
    @7
    @9
    @22
    simp22
    #
    cA
    cP
    cR
    cT
    cG
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
    trljat1
    syl3anc
    @23
    @25
    @31
    @26
    @32
    c.or
    @25
    @31
    wceq
    @23
    cP
    cO
    @30
    cdlemk1.o
    fveq1i
    a1i
    @23
    @0
    @5
    @2
    @26
    @32
    wceq
    @37
    @38
    @0
    @1
    @2
    @10
    @22
    simp13
    #
    cR
    cT
    cG
    cD
    cH
    cK
    cW
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    trlcocnv
    syl3anc
    oveq12d
    oveq12d
    @23
    @0
    @9
    @5
    @1
    @2
    @4
    @17
    @16
    @18
    wne
    #
    wa
    @12
    @14
    @13
    w3a
    #
    @7
    @35
    @28
    wceq
    @37
    @3
    @6
    @7
    @9
    @22
    simp23
    #
    @38
    @0
    @1
    @2
    @10
    @22
    simp12
    #
    @40
    @4
    @5
    @7
    @9
    @3
    @22
    simp21l
    #
    @23
    @17
    @41
    @17
    @19
    @20
    @15
    @3
    @10
    simp3r1
    #
    @23
    @18
    @16
    @17
    @19
    @20
    @15
    @3
    @10
    simp3r2
    #
    necomd
    jca
    @23
    @12
    @14
    @13
    @12
    @13
    @14
    @21
    @3
    @10
    simp3l1
    @12
    @13
    @14
    @21
    @3
    @10
    simp3l3
    @12
    @13
    @14
    @21
    @3
    @10
    simp3l2
    3jca
    #
    @39
    cA
    cB
    cD
    cP
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cG
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
    cdlemk1.u
    cdlemkuv2
    syl333anc
    @23
    @0
    @1
    @5
    @4
    @2
    wa
    @7
    @9
    @42
    @20
    @17
    wa
    @19
    @36
    @34
    wceq
    @37
    @44
    @38
    @23
    @4
    @2
    @45
    @40
    jca
    @39
    @43
    @48
    @23
    @20
    @17
    @17
    @19
    @20
    @15
    @3
    @10
    simp3r3
    @46
    jca
    @47
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cD
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.m
    cdlemk1.s
    cdlemk12
    syl333anc
    3eqtr4rd
end
