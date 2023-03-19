include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "wne.mm"
include "w3a.mm"
include "co.mm"
include "cif.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpl3l.mm"
include "simpl3r.mm"
include "simpr.mm"
include "cdleme25cl.mm"
include "syl312anc.mm"
include "simp1l.mm"
include "simp1r.mm"
include "simp2ll.mm"
include "simp2rl.mm"
include "simp3ll.mm"
include "cdleme1b.mm"
include "syl23anc.mm"
include "adantr.mm"
include "ifclda.mm"
include "syl5eqel.mm"

theorem cdleme27cl
  let vz: setvar z
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vs: setvar s
  let vt: setvar t
  let cG: class G
  let cO: class O
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

  disjoint s u
  disjoint s z
  disjoint A s
  disjoint u z
  disjoint A u
  disjoint A z
  disjoint B s
  disjoint B u
  disjoint B z
  disjoint F u
  disjoint H s
  disjoint H z
  disjoint .\/ s
  disjoint .\/ u
  disjoint .\/ z
  disjoint K s
  disjoint K z
  disjoint .<_ s
  disjoint .<_ u
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ u
  disjoint ./\ z
  disjoint N u
  disjoint P s
  disjoint P u
  disjoint P z
  disjoint Q s
  disjoint Q u
  disjoint Q z
  disjoint U s
  disjoint U u
  disjoint U z
  disjoint W s
  disjoint W u
  disjoint W z
  disjoint s t
  disjoint t u
  disjoint t z
  disjoint A t
  disjoint B t
  disjoint G u
  disjoint H t
  disjoint .\/ t
  disjoint K t
  disjoint .<_ t
  disjoint ./\ t
  disjoint N t
  disjoint O s
  disjoint O u
  disjoint P t
  disjoint Q t
  disjoint U t
  disjoint V z
  disjoint W t
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( s e. A /\ -. s .<_ W ) /\ P =/= Q ) ) -> C e. B )

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
    wa
    #
    vs
    cv
    #
    cA
    wcel
    #
    @10
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    cP
    cQ
    wne
    #
    wa
    #
    w3a
    #
    cC
    @10
    cP
    cQ
    c.or
    co
    c.le
    wbr
    #
    cD
    cF
    cif
    cB
    cdleme27.c
    @16
    @17
    cD
    cF
    cB
    @16
    @17
    wa
    @2
    @5
    @8
    @13
    @14
    @17
    cD
    cB
    wcel
    @2
    @9
    @15
    @17
    simpl1
    @5
    @8
    @2
    @15
    @17
    simpl2l
    @5
    @8
    @2
    @15
    @17
    simpl2r
    @13
    @14
    @2
    @9
    @17
    simpl3l
    @13
    @14
    @2
    @9
    @17
    simpl3r
    @16
    @17
    simpr
    vu
    cA
    cB
    cP
    cQ
    @10
    cU
    cZ
    cH
    cD
    c.or
    cK
    c.le
    c.an
    cN
    cW
    vz
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.z
    cdleme27.n
    cdleme27.d
    cdleme25cl
    syl312anc
    @16
    cF
    cB
    wcel
    #
    @17
    wn
    @16
    @0
    @1
    @3
    @6
    @11
    @18
    @0
    @1
    @9
    @15
    simp1l
    @0
    @1
    @9
    @15
    simp1r
    @3
    @4
    @8
    @2
    @15
    simp2ll
    @6
    @7
    @5
    @2
    @15
    simp2rl
    @11
    @12
    @14
    @2
    @9
    simp3ll
    cA
    cB
    cP
    cQ
    @10
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.f
    cdleme26.b
    cdleme1b
    syl23anc
    adantr
    ifclda
    syl5eqel
end
