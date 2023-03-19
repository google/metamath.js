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
include "simp11l.mm"
include "simp11r.mm"
include "simp33.mm"
include "cdlemk16a.mm"
include "ltrniotacl.mm"
include "syl211anc.mm"

theorem cdlemkj
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
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
  let cZ: class Z
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
  assume cdlemk.z: |- Z = ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` G ) ) ./\ ( ( O ` P ) .\/ ( R ` ( G o. `' D ) ) ) ) )

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
  disjoint G j
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) /\ G e. T ) /\ ( F e. T /\ D e. T /\ N e. T ) /\ ( ( ( R ` D ) =/= ( R ` F ) /\ ( R ` D ) =/= ( R ` G ) ) /\ ( F =/= ( _I |` B ) /\ G =/= ( _I |` B ) /\ D =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> Z e. T )

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
    cD
    cT
    wcel
    cN
    cT
    wcel
    w3a
    #
    cD
    cR
    cfv
    #
    @2
    wne
    @7
    cG
    cR
    cfv
    #
    wne
    wa
    #
    cF
    cid
    cB
    cres
    #
    wne
    cG
    @10
    wne
    cD
    @10
    wne
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
    @0
    @1
    @12
    cP
    @8
    c.or
    co
    cP
    cO
    cfv
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
    @14
    cW
    c.le
    wbr
    wn
    wa
    cZ
    cT
    wcel
    @0
    @1
    @3
    @4
    @6
    @13
    simp11l
    @0
    @1
    @3
    @4
    @6
    @13
    simp11r
    @5
    @6
    @9
    @11
    @12
    simp33
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
    cG
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
    cdlemk16a
    cA
    cP
    @14
    cT
    vj
    cZ
    cH
    cK
    c.le
    cW
    cdlemk1.l
    cdlemk1.a
    cdlemk1.h
    cdlemk1.t
    cdlemk.z
    ltrniotacl
    syl211anc
end
