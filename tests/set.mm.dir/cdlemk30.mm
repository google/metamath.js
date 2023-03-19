include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "w3a.mm"
include "wne.mm"
include "cid.mm"
include "cres.mm"
include "wbr.mm"
include "wn.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "simp1l.mm"
include "simp21.mm"
include "simp22.mm"
include "simp23.mm"
include "simp33.mm"
include "simp1r.mm"
include "simp32l.mm"
include "simp32r.mm"
include "simp31.mm"
include "cdlemksv2.mm"
include "syl333anc.mm"

theorem cdlemk30
  let cA: class A
  let cB: class B
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
  let cW: class W
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vj: setvar j
  let cD: class D
  let cG: class G
  let cQ: class Q
  assume cdlemk3.b: |- B = ( Base ` K )
  assume cdlemk3.l: |- .<_ = ( le ` K )
  assume cdlemk3.j: |- .\/ = ( join ` K )
  assume cdlemk3.m: |- ./\ = ( meet ` K )
  assume cdlemk3.a: |- A = ( Atoms ` K )
  assume cdlemk3.h: |- H = ( LHyp ` K )
  assume cdlemk3.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk3.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk3.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )

  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
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
  disjoint b f
  disjoint b i
  disjoint d e
  disjoint d f
  disjoint d i
  disjoint ./\ d
  disjoint e f
  disjoint e i
  disjoint ./\ e
  disjoint .\/ d
  disjoint .\/ e
  disjoint d j
  disjoint D d
  disjoint e j
  disjoint D e
  disjoint f j
  disjoint D f
  disjoint i j
  disjoint D i
  disjoint D j
  disjoint G d
  disjoint G e
  disjoint G j
  disjoint P d
  disjoint P e
  disjoint Q d
  disjoint Q e
  disjoint R d
  disjoint R e
  disjoint T d
  disjoint T e
  disjoint W d
  disjoint W e
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( R ` F ) = ( R ` N ) ) /\ ( F e. T /\ b e. T /\ N e. T ) /\ ( ( R ` b ) =/= ( R ` F ) /\ ( F =/= ( _I |` B ) /\ b =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( S ` b ) ` P ) = ( ( P .\/ ( R ` b ) ) ./\ ( ( N ` P ) .\/ ( R ` ( b o. `' F ) ) ) ) )

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
    wa
    #
    cF
    cT
    wcel
    #
    vb
    cv
    #
    cT
    wcel
    #
    cN
    cT
    wcel
    #
    w3a
    #
    @5
    cR
    cfv
    #
    @1
    wne
    #
    cF
    cid
    cB
    cres
    #
    wne
    #
    @5
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
    @0
    @4
    @6
    @7
    @15
    @2
    @12
    @13
    @10
    cP
    @5
    cS
    cfv
    cfv
    cP
    @9
    c.or
    co
    cP
    cN
    cfv
    @5
    cF
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    @0
    @2
    @8
    @16
    simp1l
    @3
    @4
    @6
    @7
    @16
    simp21
    @3
    @4
    @6
    @7
    @16
    simp22
    @3
    @4
    @6
    @7
    @16
    simp23
    @3
    @8
    @10
    @14
    @15
    simp33
    @0
    @2
    @8
    @16
    simp1r
    @12
    @13
    @10
    @15
    @3
    @8
    simp32l
    @12
    @13
    @10
    @15
    @3
    @8
    simp32r
    @3
    @8
    @10
    @14
    @15
    simp31
    cA
    cB
    cP
    cR
    cS
    cT
    vf
    vi
    cF
    @5
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cdlemk3.b
    cdlemk3.l
    cdlemk3.j
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemk3.m
    cdlemk3.s
    cdlemksv2
    syl333anc
end
