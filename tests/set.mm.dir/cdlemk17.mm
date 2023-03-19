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
include "cdlemk15.mm"
include "cal.mm"
include "wb.mm"
include "simp11l.mm"
include "hlatl.mm"
include "syl.mm"
include "simp11.mm"
include "simp21.mm"
include "simp22l.mm"
include "ltrnat.mm"
include "syl3anc.mm"
include "cdlemk16.mm"
include "simpld.mm"
include "atcmp.mm"
include "mpbid.mm"

theorem cdlemk17
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ ( R ` D ) =/= ( R ` F ) ) ) -> ( N ` P ) = ( ( P .\/ ( R ` F ) ) ./\ ( ( O ` P ) .\/ ( R ` ( F o. `' D ) ) ) ) )

  proof
    cK
    chlt
    wcel
    #
    cW
    cH
    wcel
    #
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
    #
    cP
    cW
    c.le
    wbr
    wn
    #
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
    cD
    @13
    wne
    cD
    cR
    cfv
    @10
    wne
    w3a
    #
    w3a
    #
    cP
    cN
    cfv
    #
    cP
    @10
    c.or
    co
    cP
    cO
    cfv
    cF
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
    c.le
    wbr
    #
    @16
    @17
    wceq
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
    cdlemk15
    @15
    cK
    cal
    wcel
    #
    @16
    cA
    wcel
    #
    @17
    cA
    wcel
    #
    @18
    @19
    wb
    @15
    @0
    @20
    @0
    @1
    @3
    @4
    @12
    @14
    simp11l
    cK
    hlatl
    syl
    @15
    @2
    @6
    @7
    @21
    @2
    @3
    @4
    @12
    @14
    simp11
    @5
    @6
    @9
    @11
    @14
    simp21
    @7
    @8
    @6
    @11
    @5
    @14
    simp22l
    cA
    cP
    cT
    cN
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    ltrnat
    syl3anc
    @15
    @22
    @17
    cW
    c.le
    wbr
    wn
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
    cdlemk16
    simpld
    cA
    @16
    @17
    cK
    c.le
    cdlemk1.l
    cdlemk1.a
    atcmp
    syl3anc
    mpbid
end
