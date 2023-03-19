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
include "simp2l1.mm"
include "simp2l2.mm"
include "simp2l3.mm"
include "simp2rl.mm"
include "simp33.mm"
include "simp13.mm"
include "simp322.mm"
include "simp323.mm"
include "simp2rr.mm"
include "3jca.mm"
include "simp31l.mm"
include "simp31r.mm"
include "simp321.mm"
include "cdlemk21N.mm"
include "syl332anc.mm"

theorem cdlemk21-2N
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
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
  disjoint X d
  disjoint X k
  assert |- ( ( ( K e. HL /\ W e. H /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ C e. T /\ N e. T ) /\ ( G e. T /\ G =/= ( _I |` B ) ) ) /\ ( ( ( R ` C ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` C ) ) /\ ( ( R ` G ) =/= ( R ` F ) /\ F =/= ( _I |` B ) /\ C =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( S ` G ) ` P ) = ( ( V ` G ) ` P ) )

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
    cG
    cT
    wcel
    #
    cG
    cid
    cB
    cres
    #
    wne
    #
    wa
    #
    wa
    #
    cC
    cR
    cfv
    #
    @2
    wne
    #
    cG
    cR
    cfv
    #
    @14
    wne
    #
    wa
    #
    @16
    @2
    wne
    #
    cF
    @10
    wne
    #
    cC
    @10
    wne
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
    @23
    @3
    @20
    @21
    @11
    w3a
    @15
    @17
    @19
    w3a
    cP
    cG
    cS
    cfv
    cfv
    cP
    cG
    cV
    cfv
    cfv
    wceq
    @25
    @0
    @1
    @0
    @1
    @3
    @13
    @24
    simp11
    @0
    @1
    @3
    @13
    @24
    simp12
    jca
    @5
    @6
    @7
    @12
    @4
    @24
    simp2l1
    @5
    @6
    @7
    @12
    @4
    @24
    simp2l2
    @25
    @7
    @9
    @5
    @6
    @7
    @12
    @4
    @24
    simp2l3
    @9
    @11
    @8
    @4
    @24
    simp2rl
    jca
    @4
    @13
    @18
    @22
    @23
    simp33
    @0
    @1
    @3
    @13
    @24
    simp13
    @25
    @20
    @21
    @11
    @19
    @20
    @21
    @18
    @23
    @4
    @13
    simp322
    @19
    @20
    @21
    @18
    @23
    @4
    @13
    simp323
    @9
    @11
    @8
    @4
    @24
    simp2rr
    3jca
    @25
    @15
    @17
    @19
    @15
    @17
    @22
    @23
    @4
    @13
    simp31l
    @15
    @17
    @22
    @23
    @4
    @13
    simp31r
    @19
    @20
    @21
    @18
    @23
    @4
    @13
    simp321
    3jca
    cA
    cB
    cC
    cP
    cR
    cS
    cT
    cV
    vd
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
    cdlemk21N
    syl332anc
end
