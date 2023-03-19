include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp21l.mm"
include "simp22l.mm"
include "simp23l.mm"
include "simp31r.mm"
include "simp33l.mm"
include "cdleme20y.mm"
include "syl132anc.mm"
include "simp11r.mm"
include "simp12l.mm"
include "simp12r.mm"
include "simp13l.mm"
include "simp31l.mm"
include "lhpat2.mm"
include "syl222anc.mm"
include "simp33r.mm"
include "oveq12d.mm"

theorem cdleme20h
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) /\ ( -. R .<_ ( S .\/ T ) /\ -. U .<_ ( S .\/ T ) ) ) ) -> ( ( ( S .\/ R ) ./\ ( T .\/ R ) ) .\/ ( ( S .\/ U ) ./\ ( T .\/ U ) ) ) = ( R .\/ U ) )

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
    cQ
    cA
    wcel
    #
    cQ
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    wn
    #
    wa
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
    cP
    cQ
    wne
    #
    cS
    cT
    wne
    #
    wa
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
    @23
    c.le
    wbr
    wn
    cR
    @23
    c.le
    wbr
    w3a
    #
    cR
    cS
    cT
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    cU
    @25
    c.le
    wbr
    wn
    #
    wa
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
    cR
    c.or
    co
    c.an
    co
    #
    cR
    cS
    cU
    c.or
    co
    cT
    cU
    c.or
    co
    c.an
    co
    #
    cU
    c.or
    @30
    @0
    @10
    @13
    @16
    @21
    @26
    @31
    cR
    wceq
    @0
    @1
    @5
    @8
    @19
    @29
    simp11l
    #
    @10
    @11
    @15
    @18
    @9
    @29
    simp21l
    @13
    @14
    @12
    @18
    @9
    @29
    simp22l
    #
    @16
    @17
    @12
    @15
    @9
    @29
    simp23l
    #
    @20
    @21
    @24
    @28
    @9
    @19
    simp31r
    #
    @26
    @27
    @22
    @24
    @9
    @19
    simp33l
    cA
    cR
    cS
    cT
    c.or
    cK
    c.le
    c.an
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme20y
    syl132anc
    @30
    @0
    cU
    cA
    wcel
    #
    @13
    @16
    @21
    @27
    @32
    cU
    wceq
    @33
    @30
    @0
    @1
    @3
    @4
    @6
    @20
    @37
    @33
    @0
    @1
    @5
    @8
    @19
    @29
    simp11r
    @3
    @4
    @2
    @8
    @19
    @29
    simp12l
    @3
    @4
    @2
    @8
    @19
    @29
    simp12r
    @6
    @7
    @2
    @5
    @19
    @29
    simp13l
    @20
    @21
    @24
    @28
    @9
    @19
    simp31l
    cA
    cP
    cQ
    cU
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme19.h
    cdleme19.u
    lhpat2
    syl222anc
    @34
    @35
    @36
    @26
    @27
    @22
    @24
    @9
    @19
    simp33r
    cA
    cU
    cS
    cT
    c.or
    cK
    c.le
    c.an
    cdleme19.l
    cdleme19.j
    cdleme19.m
    cdleme19.a
    cdleme20y
    syl132anc
    oveq12d
end
