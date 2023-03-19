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
include "co.mm"
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
include "cdlemkole.mm"
include "syl333anc.mm"

theorem cdlemkole-2N
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
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
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
  assert |- ( ( ( K e. HL /\ W e. H /\ ( R ` F ) = ( R ` N ) ) /\ ( F e. T /\ C e. T /\ N e. T ) /\ ( ( R ` C ) =/= ( R ` F ) /\ ( F =/= ( _I |` B ) /\ C =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( Q ` P ) .<_ ( P .\/ ( R ` C ) ) )

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
    #
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
    @11
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
    @15
    @3
    @12
    @13
    @10
    cP
    cQ
    cfv
    cP
    @9
    c.or
    co
    c.le
    wbr
    @17
    @0
    @1
    @0
    @1
    @3
    @8
    @16
    simp11
    @0
    @1
    @3
    @8
    @16
    simp12
    jca
    @4
    @5
    @6
    @7
    @16
    simp21
    @4
    @5
    @6
    @7
    @16
    simp22
    @4
    @5
    @6
    @7
    @16
    simp23
    @4
    @8
    @10
    @14
    @15
    simp33
    @0
    @1
    @3
    @8
    @16
    simp13
    @12
    @13
    @10
    @15
    @4
    @8
    simp32l
    @12
    @13
    @10
    @15
    @4
    @8
    simp32r
    @4
    @8
    @10
    @14
    @15
    simp31
    cA
    cB
    cC
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
    cdlemkole
    syl333anc
end
