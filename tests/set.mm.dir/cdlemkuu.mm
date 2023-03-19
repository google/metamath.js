include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "ccnv.mm"
include "ccom.mm"
include "wceq.mm"
include "crio.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "cnveq.mm"
include "coeq2d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "riotabidv.mm"
include "coeq1.mm"
include "riotaex.mm"
include "ovmpt2.mm"
include "cdlemksv.mm"
include "adantl.mm"
include "eqtr4d.mm"

theorem cdlemkuu
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
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
  let cZ: class Z
  let vd: setvar d
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
  assume cdlemk3.o2: |- Q = ( S ` D )
  assume cdlemk3.u2: |- Z = ( e e. T |-> ( iota_ j e. T ( j ` P ) = ( ( P .\/ ( R ` e ) ) ./\ ( ( Q ` P ) .\/ ( R ` ( e o. `' D ) ) ) ) ) )

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
  disjoint Q d
  disjoint Q e
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
  disjoint b f
  disjoint b i
  assert |- ( ( D e. T /\ G e. T ) -> ( D Y G ) = ( Z ` G ) )

  proof
    cD
    cT
    wcel
    #
    cG
    cT
    wcel
    #
    wa
    cD
    cG
    cY
    co
    cP
    vj
    cv
    cfv
    #
    cP
    cG
    cR
    cfv
    #
    c.or
    co
    #
    cP
    cQ
    cfv
    #
    cG
    cD
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    vj
    cT
    crio
    #
    cG
    cZ
    cfv
    #
    vd
    ve
    cD
    cG
    cT
    cT
    @2
    cP
    ve
    cv
    #
    cR
    cfv
    #
    c.or
    co
    #
    cP
    vd
    cv
    #
    cS
    cfv
    #
    cfv
    #
    @14
    @17
    ccnv
    #
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    vj
    cT
    crio
    @12
    cY
    @2
    @16
    @5
    @14
    @6
    ccom
    #
    cR
    cfv
    #
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    vj
    cT
    crio
    @17
    cD
    wceq
    #
    @25
    @30
    vj
    cT
    @31
    @24
    @29
    @2
    @31
    @23
    @28
    @16
    c.an
    @31
    @19
    @5
    @22
    @27
    c.or
    @31
    cP
    @18
    cQ
    @31
    @18
    cD
    cS
    cfv
    cQ
    @17
    cD
    cS
    fveq2
    cdlemk3.o2
    syl6eqr
    fveq1d
    @31
    @21
    @26
    cR
    @31
    @20
    @6
    @14
    @17
    cD
    cnveq
    coeq2d
    fveq2d
    oveq12d
    oveq2d
    eqeq2d
    riotabidv
    @14
    cG
    wceq
    #
    @30
    @11
    vj
    cT
    @32
    @29
    @10
    @2
    @32
    @16
    @4
    @28
    @9
    c.an
    @32
    @15
    @3
    cP
    c.or
    @14
    cG
    cR
    fveq2
    oveq2d
    @32
    @27
    @8
    @5
    c.or
    @32
    @26
    @7
    cR
    @14
    cG
    @6
    coeq1
    fveq2d
    oveq2d
    oveq12d
    eqeq2d
    riotabidv
    cdlemk3.u1
    @11
    vj
    cT
    riotaex
    ovmpt2
    @1
    @13
    @12
    wceq
    @0
    cA
    cB
    cP
    cR
    cZ
    cT
    ve
    vj
    cD
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cQ
    cW
    cdlemk3.b
    cdlemk3.l
    cdlemk3.j
    cdlemk3.a
    cdlemk3.h
    cdlemk3.t
    cdlemk3.r
    cdlemk3.m
    cdlemk3.u2
    cdlemksv
    adantl
    eqtr4d
end
