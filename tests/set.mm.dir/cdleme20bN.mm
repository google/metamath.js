include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "clat.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1l.mm"
include "hllat.mm"
include "syl.mm"
include "simp22l.mm"
include "eqid.mm"
include "atbase.mm"
include "simp21.mm"
include "simp23l.mm"
include "latj31.mm"
include "syl13anc.mm"
include "oveq1d.mm"
include "simp1r.mm"
include "simp22r.mm"
include "simp31.mm"
include "simp33.mm"
include "cdleme20aN.mm"
include "syl233anc.mm"
include "hlatjcom.mm"
include "syl3anc.mm"
include "syl5eq.mm"
include "simp23r.mm"
include "simp32.mm"
include "eqtrd.mm"
include "3eqtr4d.mm"

theorem cdleme20bN
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
  let cV: class V
  let cW: class W
  let cY: class Y
  assume cdleme19.l: |- .<_ = ( le ` K )
  assume cdleme19.j: |- .\/ = ( join ` K )
  assume cdleme19.m: |- ./\ = ( meet ` K )
  assume cdleme19.a: |- A = ( Atoms ` K )
  assume cdleme19.h: |- H = ( LHyp ` K )
  assume cdleme19.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme19.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme19.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme19.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme19.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme20.v: |- V = ( ( S .\/ T ) ./\ W )


  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( R e. A /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) ) -> ( V .\/ D ) = ( V .\/ Y ) )

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
    cR
    cA
    wcel
    #
    cS
    cA
    wcel
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cT
    cA
    wcel
    #
    cT
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
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
    #
    cT
    @11
    c.le
    wbr
    wn
    #
    cR
    @11
    c.le
    wbr
    #
    w3a
    #
    w3a
    #
    cS
    cR
    c.or
    co
    cT
    c.or
    co
    #
    cW
    c.an
    co
    #
    cT
    cR
    c.or
    co
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cV
    cD
    c.or
    co
    #
    cV
    cY
    c.or
    co
    #
    @16
    @17
    @19
    cW
    c.an
    @16
    cK
    clat
    wcel
    #
    cS
    cK
    cbs
    cfv
    #
    wcel
    #
    cR
    @24
    wcel
    #
    cT
    @24
    wcel
    #
    @17
    @19
    wceq
    @16
    @0
    @23
    @0
    @1
    @10
    @15
    simp1l
    #
    cK
    hllat
    syl
    @16
    @4
    @25
    @4
    @5
    @3
    @9
    @2
    @15
    simp22l
    #
    cA
    @24
    cS
    cK
    @24
    eqid
    #
    cdleme19.a
    atbase
    syl
    @16
    @3
    @26
    @2
    @3
    @6
    @9
    @15
    simp21
    #
    cA
    @24
    cR
    cK
    @30
    cdleme19.a
    atbase
    syl
    @16
    @7
    @27
    @7
    @8
    @3
    @6
    @2
    @15
    simp23l
    #
    cA
    @24
    cT
    cK
    @30
    cdleme19.a
    atbase
    syl
    @24
    c.or
    cK
    cS
    cR
    cT
    @30
    cdleme19.j
    latj31
    syl13anc
    oveq1d
    @16
    @0
    @1
    @3
    @4
    @5
    @7
    @12
    @14
    @21
    @18
    wceq
    @28
    @0
    @1
    @10
    @15
    simp1r
    #
    @31
    @29
    @4
    @5
    @3
    @9
    @2
    @15
    simp22r
    @32
    @2
    @10
    @12
    @13
    @14
    simp31
    @2
    @10
    @12
    @13
    @14
    simp33
    #
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
    cV
    cW
    cY
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.f
    cdleme19.g
    cdleme19.d
    cdleme19.y
    cdleme20.v
    cdleme20aN
    syl233anc
    @16
    @22
    cT
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cY
    c.or
    co
    #
    @20
    @16
    cV
    @36
    cY
    c.or
    @16
    cV
    cS
    cT
    c.or
    co
    #
    cW
    c.an
    co
    @36
    cdleme20.v
    @16
    @38
    @35
    cW
    c.an
    @16
    @0
    @4
    @7
    @38
    @35
    wceq
    @28
    @29
    @32
    cA
    c.or
    cK
    cS
    cT
    cdleme19.j
    cdleme19.a
    hlatjcom
    syl3anc
    oveq1d
    syl5eq
    oveq1d
    @16
    @0
    @1
    @3
    @7
    @8
    @4
    @13
    @14
    @37
    @20
    wceq
    @28
    @33
    @31
    @32
    @7
    @8
    @3
    @6
    @2
    @15
    simp23r
    @29
    @2
    @10
    @12
    @13
    @14
    simp32
    @34
    cA
    cY
    cP
    cQ
    cR
    cT
    cS
    cU
    cG
    cF
    cH
    c.or
    cK
    c.le
    c.an
    @36
    cW
    cD
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    cdleme19.g
    cdleme19.f
    cdleme19.y
    cdleme19.d
    @36
    eqid
    cdleme20aN
    syl233anc
    eqtrd
    3eqtr4d
end
