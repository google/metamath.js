include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "simp1.mm"
include "simp22.mm"
include "simp23.mm"
include "simp21.mm"
include "simp31.mm"
include "simp321.mm"
include "simp322.mm"
include "jca.mm"
include "simp323.mm"
include "3jca.mm"
include "cdleme20f.mm"
include "syl131anc.mm"
include "cdleme20h.mm"
include "wceq.mm"
include "cdleme20g.mm"
include "simp11.mm"
include "simp12l.mm"
include "simp13l.mm"
include "cdleme4.mm"
include "3eqtr4d.mm"
include "breqtrd.mm"

theorem cdleme20i
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


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) ) /\ ( ( P =/= Q /\ S =/= T ) /\ ( -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) /\ R .<_ ( P .\/ Q ) ) /\ ( -. R .<_ ( S .\/ T ) /\ -. U .<_ ( S .\/ T ) ) ) ) -> ( ( F .\/ D ) ./\ ( G .\/ Y ) ) .<_ ( P .\/ Q ) )

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
    cS
    cT
    wne
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
    #
    cT
    @13
    c.le
    wbr
    wn
    #
    cR
    @13
    c.le
    wbr
    #
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
    cU
    @18
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    w3a
    #
    cF
    cD
    c.or
    co
    cG
    cY
    c.or
    co
    c.an
    co
    #
    cD
    cS
    c.or
    co
    cY
    cT
    c.or
    co
    c.an
    co
    cS
    cF
    c.or
    co
    cT
    cG
    c.or
    co
    c.an
    co
    c.or
    co
    #
    @13
    c.le
    @21
    @7
    @9
    @10
    @8
    @12
    @14
    @15
    wa
    #
    @16
    w3a
    #
    @22
    @23
    c.le
    wbr
    @7
    @11
    @20
    simp1
    #
    @7
    @8
    @9
    @10
    @20
    simp22
    #
    @7
    @8
    @9
    @10
    @20
    simp23
    #
    @7
    @8
    @9
    @10
    @20
    simp21
    #
    @21
    @12
    @24
    @16
    @7
    @11
    @12
    @17
    @19
    simp31
    @21
    @14
    @15
    @14
    @15
    @16
    @12
    @19
    @7
    @11
    simp321
    @14
    @15
    @16
    @12
    @19
    @7
    @11
    simp322
    jca
    @14
    @15
    @16
    @12
    @19
    @7
    @11
    simp323
    #
    3jca
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
    cdleme20f
    syl131anc
    @21
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
    c.or
    co
    #
    cR
    cU
    c.or
    co
    #
    @23
    @13
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
    cdleme20h
    @21
    @7
    @9
    @10
    @8
    @25
    @23
    @32
    wceq
    @26
    @27
    @28
    @29
    @31
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
    cdleme20g
    syl131anc
    @21
    @0
    @1
    @4
    @8
    @16
    @13
    @33
    wceq
    @0
    @3
    @6
    @11
    @20
    simp11
    @1
    @2
    @0
    @6
    @11
    @20
    simp12l
    @4
    @5
    @0
    @3
    @11
    @20
    simp13l
    @29
    @30
    cA
    cP
    cQ
    cR
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
    cdleme4
    syl131anc
    3eqtr4d
    breqtrd
end
