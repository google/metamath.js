include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "3eqtr4g.mm"
include "eqeq1d.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl3l.mm"
include "simpr.mm"
include "jca.mm"
include "simpl3r.mm"
include "cdleme21.mm"
include "syl332anc.mm"
include "eqidd.mm"
include "pm2.61ne.mm"

theorem cdleme21k
  let cA: class A
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
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
  let cY: class Y
  let vr: setvar r
  let vz: setvar z
  assume cdleme21.l: |- .<_ = ( le ` K )
  assume cdleme21.j: |- .\/ = ( join ` K )
  assume cdleme21.m: |- ./\ = ( meet ` K )
  assume cdleme21.a: |- A = ( Atoms ` K )
  assume cdleme21.h: |- H = ( LHyp ` K )
  assume cdleme21.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme21.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme21g.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme21g.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme21g.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme21g.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ D ) )
  assume cdleme21g.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ Y ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( P =/= Q /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) ) ) -> N = O )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    cS
    cA
    wcel
    cS
    cW
    c.le
    wbr
    wn
    wa
    #
    cT
    cA
    wcel
    cT
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cS
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    cT
    @9
    c.le
    wbr
    wn
    cR
    @9
    c.le
    wbr
    w3a
    #
    wa
    #
    w3a
    #
    cN
    cO
    wceq
    #
    cO
    cO
    wceq
    cS
    cT
    cS
    cT
    wceq
    #
    cN
    cO
    cO
    @14
    @9
    cF
    cD
    c.or
    co
    #
    c.an
    co
    @9
    cG
    cY
    c.or
    co
    #
    c.an
    co
    cN
    cO
    @14
    @15
    @16
    @9
    c.an
    @14
    cF
    cG
    cD
    cY
    c.or
    @14
    cS
    cU
    c.or
    co
    #
    cQ
    cP
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cT
    cU
    c.or
    co
    #
    cQ
    cP
    cT
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cF
    cG
    @14
    @17
    @21
    @20
    @24
    c.an
    cS
    cT
    cU
    c.or
    oveq1
    @14
    @19
    @23
    cQ
    c.or
    @14
    @18
    @22
    cW
    c.an
    cS
    cT
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    cdleme21.f
    cdleme21g.g
    3eqtr4g
    @14
    cR
    cS
    c.or
    co
    #
    cW
    c.an
    co
    cR
    cT
    c.or
    co
    #
    cW
    c.an
    co
    cD
    cY
    @14
    @25
    @26
    cW
    c.an
    cS
    cT
    cR
    c.or
    oveq2
    oveq1d
    cdleme21g.d
    cdleme21g.y
    3eqtr4g
    oveq12d
    oveq2d
    cdleme21g.n
    cdleme21g.o
    3eqtr4g
    eqeq1d
    @12
    cS
    cT
    wne
    #
    wa
    #
    @0
    @1
    @2
    @4
    @5
    @6
    @8
    @27
    wa
    @10
    @13
    @0
    @1
    @2
    @7
    @11
    @27
    simpl11
    @0
    @1
    @2
    @7
    @11
    @27
    simpl12
    @0
    @1
    @2
    @7
    @11
    @27
    simpl13
    @4
    @5
    @6
    @3
    @11
    @27
    simpl21
    @4
    @5
    @6
    @3
    @11
    @27
    simpl22
    @4
    @5
    @6
    @3
    @11
    @27
    simpl23
    @28
    @8
    @27
    @8
    @10
    @3
    @7
    @27
    simpl3l
    @12
    @27
    simpr
    jca
    @8
    @10
    @3
    @7
    @27
    simpl3r
    cA
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
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
    cY
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21.f
    cdleme21g.g
    cdleme21g.d
    cdleme21g.y
    cdleme21g.n
    cdleme21g.o
    cdleme21
    syl332anc
    @12
    cO
    eqidd
    pm2.61ne
end
