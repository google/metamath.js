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
include "fveq1i.mm"
include "cdlemksv2.mm"
include "syl5eq.mm"

theorem cdlemk13
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( N e. T /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ ( R ` D ) =/= ( R ` F ) ) ) -> ( O ` P ) = ( ( P .\/ ( R ` D ) ) ./\ ( ( N ` P ) .\/ ( R ` ( D o. `' F ) ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    cF
    cT
    wcel
    cD
    cT
    wcel
    w3a
    cN
    cT
    wcel
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
    w3a
    cF
    cid
    cB
    cres
    #
    wne
    cD
    @1
    wne
    cD
    cR
    cfv
    #
    @0
    wne
    w3a
    w3a
    cP
    cO
    cfv
    cP
    cD
    cS
    cfv
    #
    cfv
    cP
    @2
    c.or
    co
    cP
    cN
    cfv
    cD
    cF
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    cP
    cO
    @3
    cdlemk1.o
    fveq1i
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    cD
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemk1.b
    cdlemk1.l
    cdlemk1.j
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk1.r
    cdlemk1.m
    cdlemk1.s
    cdlemksv2
    syl5eq
end
