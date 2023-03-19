include "chlt.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "wne.mm"
include "cid.mm"
include "cres.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "simp11.mm"
include "simp12.mm"
include "jca.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp33.mm"
include "simp13.mm"
include "simp32l.mm"
include "simp32r.mm"
include "simp31.mm"
include "cdlemk18.mm"
include "syl333anc.mm"

theorem cdlemk18-2N
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
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  let vd: setvar d
  let cG: class G
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
  disjoint G d
  disjoint G k
  assert |- ( ( ( K e. HL /\ W e. H /\ ( R ` F ) = ( R ` N ) ) /\ ( F e. T /\ C e. T /\ N e. T ) /\ ( ( R ` C ) =/= ( R ` F ) /\ ( F =/= ( _I |` B ) /\ C =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( N ` P ) = ( ( V ` F ) ` P ) )

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
    cC
    cR
    cfv
    @2
    wne
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cC
    @10
    wne
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
    @14
    @3
    @11
    @12
    @9
    cP
    cN
    cfv
    cP
    cF
    cV
    cfv
    cfv
    wceq
    @16
    @0
    @1
    @0
    @1
    @3
    @8
    @15
    simp11
    @0
    @1
    @3
    @8
    @15
    simp12
    jca
    @4
    @5
    @6
    @7
    @15
    simp21
    @4
    @5
    @6
    @7
    @15
    simp22
    @4
    @5
    @6
    @7
    @15
    simp23
    @4
    @8
    @9
    @13
    @14
    simp33
    @0
    @1
    @3
    @8
    @15
    simp13
    @11
    @12
    @9
    @14
    @4
    @8
    simp32l
    @11
    @12
    @9
    @14
    @4
    @8
    simp32r
    @4
    @8
    @9
    @13
    @14
    simp31
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
    cdlemk18
    syl333anc
end
