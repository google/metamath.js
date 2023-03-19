include "chlt.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "wne.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "simp11.mm"
include "simp12.mm"
include "jca.mm"
include "simp211.mm"
include "simp212.mm"
include "simp213.mm"
include "simp22l.mm"
include "simp33.mm"
include "simp13.mm"
include "simp32l.mm"
include "simp32r.mm"
include "simp22r.mm"
include "3jca.mm"
include "simp31.mm"
include "cdlemk20.mm"
include "syl332anc.mm"

theorem cdlemk20-2N
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let cF: class F
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
  let cG: class G
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
  disjoint i k
  disjoint f k
  disjoint D k
  disjoint d i
  disjoint D i
  disjoint d f
  disjoint D f
  disjoint D d
  disjoint G d
  disjoint G k
  disjoint X d
  disjoint X k
  disjoint G i
  disjoint G f
  assert |- ( ( ( K e. HL /\ W e. H /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ C e. T /\ N e. T ) /\ ( D e. T /\ D =/= ( _I |` B ) ) /\ ( C e. T /\ C =/= ( _I |` B ) ) ) /\ ( ( ( R ` C ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` C ) ) /\ ( F =/= ( _I |` B ) /\ C =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( V ` D ) ` P ) = ( O ` P ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
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
    cT
    wcel
    #
    cC
    cT
    wcel
    #
    cN
    cT
    wcel
    #
    w3a
    #
    cD
    cT
    wcel
    #
    cD
    cid
    cB
    cres
    #
    wne
    #
    wa
    #
    @6
    cC
    @10
    wne
    #
    wa
    #
    w3a
    #
    cC
    cR
    cfv
    #
    @2
    wne
    cD
    cR
    cfv
    #
    @2
    wne
    @17
    @16
    wne
    w3a
    #
    cF
    @10
    wne
    #
    @13
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
    w3a
    #
    w3a
    #
    @0
    @1
    wa
    @5
    @6
    @7
    @9
    wa
    @21
    @3
    @19
    @13
    @11
    w3a
    @18
    cP
    cD
    cV
    cfv
    cfv
    cP
    cO
    cfv
    wceq
    @23
    @0
    @1
    @0
    @1
    @3
    @15
    @22
    simp11
    @0
    @1
    @3
    @15
    @22
    simp12
    jca
    @5
    @6
    @7
    @12
    @14
    @4
    @22
    simp211
    @5
    @6
    @7
    @12
    @14
    @4
    @22
    simp212
    @23
    @7
    @9
    @5
    @6
    @7
    @12
    @14
    @4
    @22
    simp213
    @9
    @11
    @8
    @14
    @4
    @22
    simp22l
    jca
    @4
    @15
    @18
    @20
    @21
    simp33
    @0
    @1
    @3
    @15
    @22
    simp13
    @23
    @19
    @13
    @11
    @19
    @13
    @18
    @21
    @4
    @15
    simp32l
    @19
    @13
    @18
    @21
    @4
    @15
    simp32r
    @9
    @11
    @8
    @14
    @4
    @22
    simp22r
    3jca
    @4
    @15
    @18
    @20
    @21
    simp31
    cA
    cB
    cD
    cC
    cP
    cO
    cR
    cS
    cT
    cV
    vd
    vf
    vi
    vk
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cQ
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
    cdlemk2.q
    cdlemk2.v
    cdlemk2a.o
    cdlemk20
    syl332anc
end
