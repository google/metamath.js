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
include "simp212.mm"
include "simp22.mm"
include "trljat1.mm"
include "syl3anc.mm"
include "simp1.mm"
include "simp211.mm"
include "simp213.mm"
include "jca.mm"
include "simp23.mm"
include "simp311.mm"
include "simp312.mm"
include "simp321.mm"
include "3jca.mm"
include "simp331.mm"
include "simp323.mm"
include "simp333.mm"
include "cdlemk20.mm"
include "syl132anc.mm"
include "eqcomd.mm"
include "trlcocnv.mm"
include "oveq12d.mm"
include "simp12.mm"
include "simp322.mm"
include "necomd.mm"
include "simp313.mm"
include "cdlemkuv2-2.mm"
include "syl333anc.mm"
include "simp31.mm"
include "simp33.mm"
include "cdlemk12u.mm"
include "syld3an3.mm"
include "3eqtr4rd.mm"

theorem cdlemk22
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
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let vd: setvar d
  let cX: class X
  assume cdlemk2.b: |- B = ( Base ` K )
  assume cdlemk2.l: |- .<_ = ( le ` K )
  assume cdlemk2.j: |- .\/ = ( join ` K )
  assume cdlemk2.m: |- ./\ = ( meet ` K )
  assume cdlemk2.a: |- A = ( Atoms ` K )
  assume cdlemk2.h: |- H = ( LHyp ` K )
  assume cdlemk2.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk2.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk2.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk2.q: |- Q = ( S ` C )
  assume cdlemk2.v: |- V = ( d e. T |-> ( iota_ k e. T ( k ` P ) = ( ( P .\/ ( R ` d ) ) ./\ ( ( Q ` P ) .\/ ( R ` ( d o. `' C ) ) ) ) ) )
  assume cdlemk2a.o: |- O = ( S ` D )
  assume cdlemk2.u: |- U = ( e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( O ` P ) .\/ ( R ` ( e o. `' D ) ) ) ) ) )

  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint C f
  disjoint C i
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
  disjoint ./\ d
  disjoint .\/ d
  disjoint C d
  disjoint d k
  disjoint G d
  disjoint G k
  disjoint Q d
  disjoint P d
  disjoint R d
  disjoint T d
  disjoint W d
  disjoint ./\ k
  disjoint .<_ k
  disjoint .\/ k
  disjoint A k
  disjoint C k
  disjoint F k
  disjoint H k
  disjoint K k
  disjoint N k
  disjoint Q k
  disjoint P k
  disjoint R k
  disjoint T k
  disjoint W k
  disjoint F d
  disjoint G i
  disjoint G f
  disjoint i k
  disjoint f k
  disjoint D k
  disjoint d i
  disjoint D i
  disjoint d f
  disjoint D f
  disjoint D d
  disjoint e j
  disjoint ./\ e
  disjoint ./\ j
  disjoint .<_ e
  disjoint .<_ j
  disjoint .\/ e
  disjoint .\/ j
  disjoint A j
  disjoint C e
  disjoint C j
  disjoint D e
  disjoint D j
  disjoint F e
  disjoint F j
  disjoint G e
  disjoint G j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint O e
  disjoint O j
  disjoint P e
  disjoint P j
  disjoint R e
  disjoint R j
  disjoint T e
  disjoint T j
  disjoint W e
  disjoint W j
  disjoint e f
  disjoint e i
  disjoint f j
  disjoint i j
  disjoint X d
  disjoint X k
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( ( N e. T /\ G e. T /\ C e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( C =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` C ) /\ ( R ` C ) =/= ( R ` F ) ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` D ) /\ ( R ` C ) =/= ( R ` D ) ) ) ) -> ( ( U ` G ) ` P ) = ( ( V ` G ) ` P ) )

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
    cC
    cT
    wcel
    #
    w3a
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
    @12
    wne
    #
    cG
    @12
    wne
    #
    w3a
    #
    cC
    @12
    wne
    #
    cG
    cR
    cfv
    #
    cC
    cR
    cfv
    #
    wne
    #
    @19
    @9
    wne
    #
    w3a
    #
    cD
    cR
    cfv
    #
    @9
    wne
    #
    @18
    @23
    wne
    #
    @19
    @23
    wne
    #
    w3a
    #
    w3a
    #
    w3a
    #
    cP
    @18
    c.or
    co
    #
    cP
    cQ
    cfv
    #
    cG
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
    cP
    cG
    cfv
    c.or
    co
    #
    cP
    cC
    cU
    cfv
    cfv
    #
    cC
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
    cV
    cfv
    cfv
    #
    cP
    cG
    cU
    cfv
    cfv
    #
    @29
    @30
    @35
    @33
    @38
    c.an
    @29
    @0
    @5
    @8
    @30
    @35
    wceq
    @0
    @1
    @2
    @11
    @28
    simp11
    #
    @4
    @5
    @6
    @8
    @10
    @3
    @28
    simp212
    #
    @3
    @7
    @8
    @10
    @28
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
    cdlemk2.l
    cdlemk2.j
    cdlemk2.a
    cdlemk2.h
    cdlemk2.t
    cdlemk2.r
    trljat1
    syl3anc
    @29
    @31
    @36
    @32
    @37
    c.or
    @29
    @36
    @31
    @29
    @3
    @4
    @6
    wa
    @8
    @10
    @13
    @14
    @17
    w3a
    @24
    @21
    @26
    w3a
    @36
    @31
    wceq
    @3
    @11
    @28
    simp1
    @29
    @4
    @6
    @4
    @5
    @6
    @8
    @10
    @3
    @28
    simp211
    #
    @4
    @5
    @6
    @8
    @10
    @3
    @28
    simp213
    #
    jca
    @44
    @3
    @7
    @8
    @10
    @28
    simp23
    #
    @29
    @13
    @14
    @17
    @13
    @14
    @15
    @22
    @27
    @3
    @11
    simp311
    #
    @13
    @14
    @15
    @22
    @27
    @3
    @11
    simp312
    @17
    @20
    @21
    @16
    @27
    @3
    @11
    simp321
    #
    3jca
    @29
    @24
    @21
    @26
    @24
    @25
    @26
    @16
    @22
    @3
    @11
    simp331
    @17
    @20
    @21
    @16
    @27
    @3
    @11
    simp323
    #
    @24
    @25
    @26
    @16
    @22
    @3
    @11
    simp333
    3jca
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    ve
    vf
    vi
    vj
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cdlemk2.b
    cdlemk2.l
    cdlemk2.j
    cdlemk2.m
    cdlemk2.a
    cdlemk2.h
    cdlemk2.t
    cdlemk2.r
    cdlemk2.s
    cdlemk2a.o
    cdlemk2.u
    cdlemk2.q
    cdlemk20
    syl132anc
    eqcomd
    @29
    @0
    @5
    @6
    @32
    @37
    wceq
    @42
    @43
    @46
    cR
    cT
    cG
    cC
    cH
    cK
    cW
    cdlemk2.h
    cdlemk2.t
    cdlemk2.r
    trlcocnv
    syl3anc
    oveq12d
    oveq12d
    @29
    @0
    @10
    @5
    @1
    @6
    @4
    @21
    @19
    @18
    wne
    #
    wa
    @13
    @15
    @17
    w3a
    @8
    @40
    @34
    wceq
    @42
    @47
    @43
    @0
    @1
    @2
    @11
    @28
    simp12
    @46
    @45
    @29
    @21
    @51
    @50
    @29
    @18
    @19
    @17
    @20
    @21
    @16
    @27
    @3
    @11
    simp322
    #
    necomd
    jca
    @29
    @13
    @15
    @17
    @48
    @13
    @14
    @15
    @22
    @27
    @3
    @11
    simp313
    @49
    3jca
    @44
    cA
    cB
    cC
    cP
    cQ
    cR
    cS
    cT
    vf
    vi
    vk
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cV
    cW
    vd
    cdlemk2.b
    cdlemk2.l
    cdlemk2.j
    cdlemk2.m
    cdlemk2.a
    cdlemk2.h
    cdlemk2.t
    cdlemk2.r
    cdlemk2.s
    cdlemk2.q
    cdlemk2.v
    cdlemkuv2-2
    syl333anc
    @3
    @11
    @28
    @16
    @17
    @20
    wa
    #
    @27
    w3a
    @41
    @39
    wceq
    @29
    @16
    @53
    @27
    @3
    @11
    @16
    @22
    @27
    simp31
    @29
    @17
    @20
    @49
    @52
    jca
    @3
    @11
    @16
    @22
    @27
    simp33
    3jca
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
    cC
    cdlemk2.b
    cdlemk2.l
    cdlemk2.j
    cdlemk2.m
    cdlemk2.a
    cdlemk2.h
    cdlemk2.t
    cdlemk2.r
    cdlemk2.s
    cdlemk2a.o
    cdlemk2.u
    cdlemk12u
    syld3an3
    3eqtr4rd
end
