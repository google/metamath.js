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
include "cv.mm"
include "ccnv.mm"
include "ccom.mm"
include "crio.mm"
include "cmpt.mm"
include "simp22.mm"
include "simp21.mm"
include "eqid.mm"
include "cdlemkuu.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "cdlemk18-2N.mm"
include "eqtr4d.mm"

theorem cdlemk18-3N
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cT: class T
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
  let cW: class W
  let cY: class Y
  let vd: setvar d
  let cG: class G
  let cQ: class Q
  let vb: setvar b
  assume cdlemk3.b: |- B = ( Base ` K )
  assume cdlemk3.l: |- .<_ = ( le ` K )
  assume cdlemk3.j: |- .\/ = ( join ` K )
  assume cdlemk3.m: |- ./\ = ( meet ` K )
  assume cdlemk3.a: |- A = ( Atoms ` K )
  assume cdlemk3.h: |- H = ( LHyp ` K )
  assume cdlemk3.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemk3.r: |- R = ( ( trL ` K ) ` W )
  assume cdlemk3.s: |- S = ( f e. T |-> ( iota_ i e. T ( i ` P ) = ( ( P .\/ ( R ` f ) ) ./\ ( ( N ` P ) .\/ ( R ` ( f o. `' F ) ) ) ) ) )
  assume cdlemk3.u1: |- Y = ( d e. T , e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( ( S ` d ) ` P ) .\/ ( R ` ( e o. `' d ) ) ) ) ) )

  disjoint d e
  disjoint d f
  disjoint d i
  disjoint ./\ d
  disjoint e f
  disjoint e i
  disjoint ./\ e
  disjoint f i
  disjoint ./\ f
  disjoint ./\ i
  disjoint .<_ i
  disjoint .\/ d
  disjoint .\/ e
  disjoint .\/ f
  disjoint .\/ i
  disjoint A i
  disjoint d j
  disjoint D d
  disjoint e j
  disjoint D e
  disjoint f j
  disjoint D f
  disjoint i j
  disjoint D i
  disjoint D j
  disjoint F f
  disjoint F i
  disjoint H i
  disjoint K i
  disjoint N f
  disjoint N i
  disjoint P d
  disjoint P e
  disjoint P f
  disjoint P i
  disjoint R d
  disjoint R e
  disjoint R f
  disjoint R i
  disjoint T d
  disjoint T e
  disjoint T f
  disjoint T i
  disjoint W d
  disjoint W e
  disjoint W f
  disjoint W i
  disjoint ./\ j
  disjoint .<_ j
  disjoint .\/ j
  disjoint A j
  disjoint F j
  disjoint H j
  disjoint K j
  disjoint N j
  disjoint P j
  disjoint R j
  disjoint S d
  disjoint S e
  disjoint S j
  disjoint T j
  disjoint W j
  disjoint F d
  disjoint F e
  disjoint G d
  disjoint G e
  disjoint G j
  disjoint Q d
  disjoint Q e
  disjoint b f
  disjoint b i
  disjoint b d
  disjoint b e
  disjoint b j
  disjoint S b
  assert |- ( ( ( K e. HL /\ W e. H /\ ( R ` F ) = ( R ` N ) ) /\ ( F e. T /\ D e. T /\ N e. T ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) ) /\ ( P e. A /\ -. P .<_ W ) ) ) -> ( ( D Y F ) ` P ) = ( N ` P ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    cF
    cR
    cfv
    #
    cN
    cR
    cfv
    wceq
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
    cD
    cR
    cfv
    @0
    wne
    cF
    cid
    cB
    cres
    #
    wne
    cD
    @5
    wne
    wa
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    w3a
    #
    cP
    cD
    cF
    cY
    co
    #
    cfv
    cP
    cF
    ve
    cT
    cP
    vj
    cv
    cfv
    cP
    ve
    cv
    #
    cR
    cfv
    c.or
    co
    cP
    cD
    cS
    cfv
    #
    cfv
    @9
    cD
    ccnv
    ccom
    cR
    cfv
    c.or
    co
    c.an
    co
    wceq
    vj
    cT
    crio
    cmpt
    #
    cfv
    #
    cfv
    cP
    cN
    cfv
    @7
    cP
    @8
    @12
    @7
    @3
    @2
    @8
    @12
    wceq
    @1
    @2
    @3
    @4
    @6
    simp22
    @1
    @2
    @3
    @4
    @6
    simp21
    cA
    cB
    cD
    cP
    @10
    cR
    cS
    cT
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
    cW
    cY
    @11
    vd
    cdlemk3.b
    cdlemk3.l
    cdlemk3.j
    cdlemk3.m
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemk3.s
    cdlemk3.u1
    @10
    eqid
    #
    @11
    eqid
    #
    cdlemkuu
    syl2anc
    fveq1d
    cA
    cB
    cD
    cP
    @10
    cR
    cS
    cT
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
    @11
    cW
    ve
    cdlemk3.b
    cdlemk3.l
    cdlemk3.j
    cdlemk3.m
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemk3.s
    @13
    @14
    cdlemk18-2N
    eqtr4d
end
