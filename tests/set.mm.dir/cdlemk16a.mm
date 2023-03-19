include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "wne.mm"
include "cid.mm"
include "cres.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp11.mm"
include "simp22.mm"
include "simp13.mm"
include "simp33.mm"
include "simp21.mm"
include "simp23.mm"
include "simp12.mm"
include "simp321.mm"
include "simp323.mm"
include "simp31l.mm"
include "cdlemkoatnle.mm"
include "syl333anc.mm"
include "cdlemkole.mm"
include "simp322.mm"
include "simp31r.mm"
include "eqid.mm"
include "cdlemh.mm"

theorem cdlemk16a
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
  let cG: class G
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) /\ G e. T ) /\ ( F e. T /\ D e. T /\ N e. T ) /\ ( ( ( R ` D ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` G ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ D =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( ( P .\/ ( R ` G ) ) ./\ ( ( O ` P ) .\/ ( R ` ( G o. `' D ) ) ) ) e. A /\ -. ( ( P .\/ ( R ` G ) ) ./\ ( ( O ` P ) .\/ ( R ` ( G o. `' D ) ) ) ) .<_ W ) )

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
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    #
    cG
    cT
    wcel
    #
    w3a
    #
    cF
    cT
    wcel
    #
    cD
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
    cR
    cfv
    #
    @1
    wne
    #
    @9
    cG
    cR
    cfv
    #
    wne
    #
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    cG
    @14
    wne
    #
    cD
    @14
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
    @6
    @3
    @19
    cP
    cO
    cfv
    #
    cA
    wcel
    @22
    cW
    c.le
    wbr
    wn
    wa
    #
    @22
    cP
    @9
    c.or
    co
    c.le
    wbr
    #
    @17
    @16
    @12
    cP
    @11
    c.or
    co
    @22
    cG
    cD
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    #
    cA
    wcel
    @25
    cW
    c.le
    wbr
    wn
    wa
    @0
    @2
    @3
    @8
    @20
    simp11
    #
    @4
    @5
    @6
    @7
    @20
    simp22
    #
    @0
    @2
    @3
    @8
    @20
    simp13
    @4
    @8
    @13
    @18
    @19
    simp33
    #
    @21
    @0
    @5
    @6
    @7
    @19
    @2
    @15
    @17
    @10
    @23
    @26
    @4
    @5
    @6
    @7
    @20
    simp21
    #
    @27
    @4
    @5
    @6
    @7
    @20
    simp23
    #
    @28
    @0
    @2
    @3
    @8
    @20
    simp12
    #
    @15
    @16
    @17
    @13
    @19
    @4
    @8
    simp321
    #
    @15
    @16
    @17
    @13
    @19
    @4
    @8
    simp323
    #
    @10
    @12
    @18
    @19
    @4
    @8
    simp31l
    #
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
    cdlemkoatnle
    syl333anc
    @21
    @0
    @5
    @6
    @7
    @19
    @2
    @15
    @17
    @10
    @24
    @26
    @29
    @27
    @30
    @28
    @31
    @32
    @33
    @34
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
    cdlemkole
    syl333anc
    @33
    @15
    @16
    @17
    @13
    @19
    @4
    @8
    simp322
    @10
    @12
    @18
    @19
    @4
    @8
    simp31r
    cA
    cB
    cP
    @22
    cR
    @25
    cT
    cD
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.m
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    @25
    eqid
    cdlemh
    syl333anc
end
