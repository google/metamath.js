include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "wceq.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "simp31.mm"
include "simp21.mm"
include "simp231.mm"
include "simp232.mm"
include "simp32l.mm"
include "jca.mm"
include "simp33.mm"
include "cdleme21d.mm"
include "syl323anc.mm"
include "cdleme21e.mm"
include "eqtr4d.mm"

theorem cdleme21f
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cE: class E
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
  let cZ: class Z
  assume cdleme21.l: |- .<_ = ( le ` K )
  assume cdleme21.j: |- .\/ = ( join ` K )
  assume cdleme21.m: |- ./\ = ( meet ` K )
  assume cdleme21.a: |- A = ( Atoms ` K )
  assume cdleme21.h: |- H = ( LHyp ` K )
  assume cdleme21.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme21.f: |- F = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme21.b: |- B = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme21.d: |- D = ( ( R .\/ S ) ./\ W )
  assume cdleme21.e: |- E = ( ( R .\/ z ) ./\ W )
  assume cdleme21d.n: |- N = ( ( P .\/ Q ) ./\ ( F .\/ D ) )
  assume cdleme21d.z: |- Z = ( ( P .\/ Q ) ./\ ( B .\/ E ) )
  assume cdleme21.g: |- G = ( ( T .\/ U ) ./\ ( Q .\/ ( ( P .\/ T ) ./\ W ) ) )
  assume cdleme21.y: |- Y = ( ( R .\/ T ) ./\ W )
  assume cdleme21.o: |- O = ( ( P .\/ Q ) ./\ ( G .\/ Y ) )


  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( T e. A /\ -. T .<_ W ) /\ ( P =/= Q /\ -. S .<_ ( P .\/ Q ) /\ -. T .<_ ( P .\/ Q ) ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( R .<_ ( P .\/ Q ) /\ U .<_ ( S .\/ T ) ) /\ ( ( z e. A /\ -. z .<_ W ) /\ ( P .\/ z ) = ( S .\/ z ) ) ) ) -> N = O )

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
    #
    cT
    @7
    c.le
    wbr
    wn
    #
    w3a
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
    cR
    @7
    c.le
    wbr
    #
    cU
    cS
    cT
    c.or
    co
    c.le
    wbr
    #
    wa
    #
    vz
    cv
    #
    cA
    wcel
    @16
    cW
    c.le
    wbr
    wn
    wa
    cP
    @16
    c.or
    co
    cS
    @16
    c.or
    co
    wceq
    wa
    #
    w3a
    #
    w3a
    #
    cN
    cZ
    cO
    @19
    @0
    @1
    @2
    @12
    @4
    @6
    @8
    @13
    wa
    @17
    cN
    cZ
    wceq
    @0
    @1
    @2
    @11
    @18
    simp11
    @0
    @1
    @2
    @11
    @18
    simp12
    @0
    @1
    @2
    @11
    @18
    simp13
    @3
    @11
    @12
    @15
    @17
    simp31
    @3
    @4
    @5
    @10
    @18
    simp21
    @6
    @8
    @9
    @4
    @5
    @3
    @18
    simp231
    @19
    @8
    @13
    @6
    @8
    @9
    @4
    @5
    @3
    @18
    simp232
    @13
    @14
    @12
    @17
    @3
    @11
    simp32l
    jca
    @3
    @11
    @12
    @15
    @17
    simp33
    vz
    cA
    cB
    cD
    cP
    cQ
    cR
    cS
    cU
    cE
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cZ
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21.f
    cdleme21.b
    cdleme21.d
    cdleme21.e
    cdleme21d.n
    cdleme21d.z
    cdleme21d
    syl323anc
    vz
    cA
    cB
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cE
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
    cZ
    cdleme21.l
    cdleme21.j
    cdleme21.m
    cdleme21.a
    cdleme21.h
    cdleme21.u
    cdleme21.f
    cdleme21.b
    cdleme21.d
    cdleme21.e
    cdleme21d.n
    cdleme21d.z
    cdleme21.g
    cdleme21.y
    cdleme21.o
    cdleme21e
    eqtr4d
end
