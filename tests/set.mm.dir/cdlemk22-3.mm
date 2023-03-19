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
include "cv.mm"
include "co.mm"
include "ccnv.mm"
include "ccom.mm"
include "crio.mm"
include "cmpt.mm"
include "eqid.mm"
include "cdlemk22.mm"
include "simp13.mm"
include "simp212.mm"
include "cdlemkuu.mm"
include "syl2anc.mm"
include "fveq1d.mm"
include "simp213.mm"
include "3eqtr4d.mm"

theorem cdlemk22-3
  let cA: class A
  let cB: class B
  let cC: class C
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
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cY: class Y
  let vd: setvar d
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
  disjoint G d
  disjoint G e
  disjoint G j
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
  disjoint .<_ e
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C i
  disjoint C j
  disjoint G f
  disjoint G i
  disjoint Q d
  disjoint Q e
  disjoint b f
  disjoint b i
  disjoint b d
  disjoint b e
  disjoint b j
  disjoint S b
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ F e. T /\ D e. T ) /\ ( ( N e. T /\ G e. T /\ C e. T ) /\ ( P e. A /\ -. P .<_ W ) /\ ( R ` F ) = ( R ` N ) ) /\ ( ( F =/= ( _I |` B ) /\ D =/= ( _I |` B ) /\ G =/= ( _I |` B ) ) /\ ( C =/= ( _I |` B ) /\ ( R ` G ) =/= ( R ` C ) /\ ( R ` C ) =/= ( R ` F ) ) /\ ( ( R ` D ) =/= ( R ` F ) /\ ( R ` G ) =/= ( R ` D ) /\ ( R ` C ) =/= ( R ` D ) ) ) ) -> ( ( D Y G ) ` P ) = ( ( C Y G ) ` P ) )

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
    cG
    cT
    wcel
    #
    cC
    cT
    wcel
    #
    w3a
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
    cD
    @11
    wne
    cG
    @11
    wne
    w3a
    cC
    @11
    wne
    cG
    cR
    cfv
    #
    cC
    cR
    cfv
    #
    wne
    @13
    @8
    wne
    w3a
    cD
    cR
    cfv
    #
    @8
    wne
    @12
    @14
    wne
    @13
    @14
    wne
    w3a
    w3a
    #
    w3a
    #
    cP
    cG
    ve
    cT
    cP
    vj
    cv
    cfv
    #
    cP
    ve
    cv
    #
    cR
    cfv
    c.or
    co
    #
    cP
    cD
    cS
    cfv
    #
    cfv
    @18
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
    cG
    ve
    cT
    @17
    @19
    cP
    cC
    cS
    cfv
    #
    cfv
    @18
    cC
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
    cD
    cG
    cY
    co
    #
    cfv
    cP
    cC
    cG
    cY
    co
    #
    cfv
    cA
    cB
    cC
    cD
    cP
    @23
    cR
    cS
    cT
    @21
    ve
    vf
    vi
    vj
    vj
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    @20
    @24
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
    @23
    eqid
    #
    @24
    eqid
    #
    @20
    eqid
    #
    @21
    eqid
    #
    cdlemk22
    @16
    cP
    @26
    @22
    @16
    @2
    @5
    @26
    @22
    wceq
    @0
    @1
    @2
    @10
    @15
    simp13
    @4
    @5
    @6
    @7
    @9
    @3
    @15
    simp212
    #
    cA
    cB
    cD
    cP
    @20
    cR
    cS
    cT
    ve
    vf
    vi
    vj
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cY
    @21
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
    @30
    @31
    cdlemkuu
    syl2anc
    fveq1d
    @16
    cP
    @27
    @25
    @16
    @6
    @5
    @27
    @25
    wceq
    @4
    @5
    @6
    @7
    @9
    @3
    @15
    simp213
    @32
    cA
    cB
    cC
    cP
    @23
    cR
    cS
    cT
    ve
    vf
    vi
    vj
    cF
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cY
    @24
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
    @28
    @29
    cdlemkuu
    syl2anc
    fveq1d
    3eqtr4d
end
