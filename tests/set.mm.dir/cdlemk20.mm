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
include "simp23.mm"
include "simp21r.mm"
include "simp12.mm"
include "simp13.mm"
include "simp21l.mm"
include "simp3r1.mm"
include "simp3r3.mm"
include "necomd.mm"
include "jca.mm"
include "simp3l1.mm"
include "simp3l3.mm"
include "simp3l2.mm"
include "3jca.mm"
include "simp22.mm"
include "cdlemkuv2.mm"
include "syl333anc.mm"
include "trljat1.mm"
include "syl3anc.mm"
include "fveq1i.mm"
include "a1i.mm"
include "trlcocnv.mm"
include "oveq12d.mm"
include "simp3r2.mm"
include "cdlemk12.mm"
include "syl5req.mm"
include "3eqtrd.mm"

theorem cdlemk20
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cG: class G
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
  assume cdlemk2a.q: |- Q = ( S ` C )

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
  disjoint e f
  disjoint e i
  disjoint C e
  disjoint f j
  disjoint C f
  disjoint i j
  disjoint C i
  disjoint C j
  disjoint G e
  disjoint G j
  disjoint X e
  disjoint X j
  disjoint G i
  disjoint G f
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( ( N e. T /\ C e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ C =/= ( _I |` B ) ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( R ` C ) =/= ( R ` F ) /\ ( R ` C ) =/= ( R ` D ) ) ) ) -> ( ( U ` C ) ` P ) = ( Q ` P ) )

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
    cC
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
    cC
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
    cC
    cR
    cfv
    #
    @8
    wne
    #
    @18
    @16
    wne
    #
    w3a
    #
    wa
    #
    w3a
    #
    cP
    cC
    cU
    cfv
    cfv
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
    cC
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
    cC
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
    cC
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
    cQ
    cfv
    #
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
    @3
    @6
    @7
    @9
    @22
    simp23
    #
    @4
    @5
    @7
    @9
    @3
    @22
    simp21r
    #
    @0
    @1
    @2
    @10
    @22
    simp12
    #
    @0
    @1
    @2
    @10
    @22
    simp13
    #
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
    @37
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
    simp3r3
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
    @3
    @6
    @7
    @9
    @22
    simp22
    #
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
    cC
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
    @25
    @30
    @28
    @34
    c.an
    @23
    @0
    @5
    @7
    @25
    @30
    wceq
    @39
    @41
    @48
    cA
    cP
    cR
    cT
    cC
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
    @26
    @32
    @27
    @33
    c.or
    @26
    @32
    wceq
    @23
    cP
    cO
    @31
    cdlemk1.o
    fveq1i
    a1i
    @23
    @0
    @5
    @2
    @27
    @33
    wceq
    @39
    @41
    @43
    cR
    cT
    cC
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
    @36
    cP
    cC
    cS
    cfv
    #
    cfv
    #
    @35
    cP
    cQ
    @49
    cdlemk2a.q
    fveq1i
    @23
    @0
    @1
    @5
    @4
    @2
    wa
    @7
    @9
    @38
    @19
    @17
    wa
    @20
    @50
    @35
    wceq
    @39
    @42
    @41
    @23
    @4
    @2
    @44
    @43
    jca
    @48
    @40
    @47
    @23
    @19
    @17
    @17
    @19
    @20
    @15
    @3
    @10
    simp3r2
    @45
    jca
    @46
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cC
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
    syl5req
    3eqtrd
end
