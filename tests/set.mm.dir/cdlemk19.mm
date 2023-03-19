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
include "simp11.mm"
include "simp21.mm"
include "simp23.mm"
include "simp12.mm"
include "simp13.mm"
include "simp33.mm"
include "jca.mm"
include "simp31.mm"
include "simp32.mm"
include "3jca.mm"
include "simp22.mm"
include "cdlemkuel.mm"
include "syl333anc.mm"
include "cdlemk18.mm"
include "cdlemd.mm"
include "syl311anc.mm"
include "eqcomd.mm"

theorem cdlemk19
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
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cG: class G
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
  disjoint G e
  disjoint G j
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ ( R ` D ) =/= ( R ` F ) ) ) -> ( U ` F ) = N )

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
    @9
    wne
    #
    cD
    cR
    cfv
    @6
    wne
    #
    w3a
    #
    w3a
    #
    cN
    cF
    cU
    cfv
    #
    @14
    @0
    @4
    @15
    cT
    wcel
    #
    @5
    cP
    cN
    cfv
    cP
    @15
    cfv
    wceq
    cN
    @15
    wceq
    @0
    @1
    @2
    @8
    @13
    simp11
    #
    @3
    @4
    @5
    @7
    @13
    simp21
    #
    @14
    @0
    @7
    @1
    @1
    @2
    @4
    @12
    @12
    wa
    @10
    @10
    @11
    w3a
    @5
    @16
    @17
    @3
    @4
    @5
    @7
    @13
    simp23
    @0
    @1
    @2
    @8
    @13
    simp12
    #
    @19
    @0
    @1
    @2
    @8
    @13
    simp13
    @18
    @14
    @12
    @12
    @3
    @8
    @10
    @11
    @12
    simp33
    #
    @20
    jca
    @14
    @10
    @10
    @11
    @3
    @8
    @10
    @11
    @12
    simp31
    #
    @21
    @3
    @8
    @10
    @11
    @12
    simp32
    3jca
    @3
    @4
    @5
    @7
    @13
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
    cdlemk1.u
    cdlemkuel
    syl333anc
    @22
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
    cdlemk18
    cA
    cP
    cT
    cN
    @15
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemd
    syl311anc
    eqcomd
end
