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
include "ccnv.mm"
include "ccom.mm"
include "co.mm"
include "simp11.mm"
include "simp12.mm"
include "jca.mm"
include "simp211.mm"
include "simp212.mm"
include "simp213.mm"
include "simp22l.mm"
include "simp23l.mm"
include "3jca.mm"
include "simp33.mm"
include "simp13.mm"
include "simp32l.mm"
include "simp32r.mm"
include "simp22r.mm"
include "simp23r.mm"
include "simp31.mm"
include "cdlemk11u.mm"
include "syl333anc.mm"

theorem cdlemk11u-2N
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
  let cX: class X
  let cZ: class Z
  let vd: setvar d
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
  assume cdlemk2.z: |- Z = ( ( ( G ` P ) .\/ ( X ` P ) ) ./\ ( ( R ` ( G o. `' C ) ) .\/ ( R ` ( X o. `' C ) ) ) )

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
  disjoint X d
  disjoint X k
  assert |- ( ( ( K e. HL /\ W e. H /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F e. T /\ C e. T /\ N e. T ) /\ ( G e. T /\ G =/= ( _I |` B ) ) /\ ( X e. T /\ X =/= ( _I |` B ) ) ) /\ ( ( ( R ` C ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` C ) /\ ( R ` X ) =/= ( R ` C ) ) /\ ( F =/= ( _I |` B ) /\ C =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( V ` G ) ` P ) .<_ ( ( ( V ` X ) ` P ) .\/ ( R ` ( X o. `' G ) ) ) )

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
    cX
    cT
    wcel
    #
    cX
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
    cG
    cR
    cfv
    @17
    wne
    cX
    cR
    cfv
    @17
    wne
    w3a
    #
    cF
    @10
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
    @9
    @13
    w3a
    @22
    @3
    @19
    @20
    @11
    w3a
    @14
    @18
    cP
    cG
    cV
    cfv
    cfv
    cP
    cX
    cV
    cfv
    cfv
    cX
    cG
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.le
    wbr
    @24
    @0
    @1
    @0
    @1
    @3
    @16
    @23
    simp11
    @0
    @1
    @3
    @16
    @23
    simp12
    jca
    @5
    @6
    @7
    @12
    @15
    @4
    @23
    simp211
    @5
    @6
    @7
    @12
    @15
    @4
    @23
    simp212
    @24
    @7
    @9
    @13
    @5
    @6
    @7
    @12
    @15
    @4
    @23
    simp213
    @9
    @11
    @8
    @15
    @4
    @23
    simp22l
    @13
    @14
    @8
    @12
    @4
    @23
    simp23l
    3jca
    @4
    @16
    @18
    @21
    @22
    simp33
    @0
    @1
    @3
    @16
    @23
    simp13
    @24
    @19
    @20
    @11
    @19
    @20
    @18
    @22
    @4
    @16
    simp32l
    @19
    @20
    @18
    @22
    @4
    @16
    simp32r
    @9
    @11
    @8
    @15
    @4
    @23
    simp22r
    3jca
    @13
    @14
    @8
    @12
    @4
    @23
    simp23r
    @4
    @16
    @18
    @21
    @22
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
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cQ
    cZ
    cW
    cX
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
    cdlemk2.z
    cdlemk11u
    syl333anc
end
