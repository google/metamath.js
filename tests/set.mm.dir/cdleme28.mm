include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "simp11.mm"
include "simp12.mm"
include "simp2l.mm"
include "simp3ll.mm"
include "jca.mm"
include "simp2r.mm"
include "simp3rl.mm"
include "simp3lr.mm"
include "simp3rr.mm"
include "simp13.mm"
include "cdleme28c.mm"
include "syl133anc.mm"
include "3exp.mm"
include "ralrimivv.mm"

theorem cdleme28
  let vz: setvar z
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
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
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let cV: class V
  assume cdleme26.b: |- B = ( Base ` K )
  assume cdleme26.l: |- .<_ = ( le ` K )
  assume cdleme26.j: |- .\/ = ( join ` K )
  assume cdleme26.m: |- ./\ = ( meet ` K )
  assume cdleme26.a: |- A = ( Atoms ` K )
  assume cdleme26.h: |- H = ( LHyp ` K )
  assume cdleme27.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme27.f: |- F = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme27.z: |- Z = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme27.n: |- N = ( ( P .\/ Q ) ./\ ( Z .\/ ( ( s .\/ z ) ./\ W ) ) )
  assume cdleme27.d: |- D = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = N ) )
  assume cdleme27.c: |- C = if ( s .<_ ( P .\/ Q ) , D , F )
  assume cdleme27.g: |- G = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme27.o: |- O = ( ( P .\/ Q ) ./\ ( Z .\/ ( ( t .\/ z ) ./\ W ) ) )
  assume cdleme27.e: |- E = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = O ) )
  assume cdleme27.y: |- Y = if ( t .<_ ( P .\/ Q ) , E , G )

  disjoint X z
  disjoint X t
  disjoint s t
  disjoint s u
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t z
  disjoint A t
  disjoint u z
  disjoint A u
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B z
  disjoint F u
  disjoint G u
  disjoint H s
  disjoint H t
  disjoint H z
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ u
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint K z
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ u
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ u
  disjoint ./\ z
  disjoint N t
  disjoint N u
  disjoint O s
  disjoint O u
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint Q z
  disjoint U s
  disjoint U t
  disjoint U u
  disjoint U z
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint W z
  disjoint X s
  disjoint V z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ P =/= Q /\ ( X e. B /\ -. X .<_ W ) ) -> A. s e. A A. t e. A ( ( ( -. s .<_ W /\ ( s .\/ ( X ./\ W ) ) = X ) /\ ( -. t .<_ W /\ ( t .\/ ( X ./\ W ) ) = X ) ) -> ( C .\/ ( X ./\ W ) ) = ( Y .\/ ( X ./\ W ) ) ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
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
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    w3a
    #
    cP
    cQ
    wne
    #
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @4
    cX
    cW
    c.an
    co
    #
    c.or
    co
    cX
    wceq
    #
    wa
    #
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @9
    @6
    c.or
    co
    cX
    wceq
    #
    wa
    #
    wa
    #
    cC
    @6
    c.or
    co
    cY
    @6
    c.or
    co
    wceq
    #
    wi
    vs
    vt
    cA
    cA
    @3
    @4
    cA
    wcel
    #
    @9
    cA
    wcel
    #
    wa
    #
    @13
    @14
    @3
    @17
    @13
    w3a
    #
    @0
    @1
    @15
    @5
    wa
    @16
    @10
    wa
    @7
    @11
    @2
    @14
    @0
    @1
    @2
    @17
    @13
    simp11
    @0
    @1
    @2
    @17
    @13
    simp12
    @18
    @15
    @5
    @3
    @15
    @16
    @13
    simp2l
    @5
    @7
    @12
    @3
    @17
    simp3ll
    jca
    @18
    @16
    @10
    @3
    @15
    @16
    @13
    simp2r
    @10
    @11
    @8
    @3
    @17
    simp3rl
    jca
    @5
    @7
    @12
    @3
    @17
    simp3lr
    @10
    @11
    @8
    @3
    @17
    simp3rr
    @0
    @1
    @2
    @17
    @13
    simp13
    vz
    vu
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
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
    cX
    cY
    cZ
    vs
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.f
    cdleme27.z
    cdleme27.n
    cdleme27.d
    cdleme27.c
    cdleme27.g
    cdleme27.o
    cdleme27.e
    cdleme27.y
    cdleme28c
    syl133anc
    3exp
    ralrimivv
end
