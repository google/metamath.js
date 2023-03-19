include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cfv.mm"
include "simpl1.mm"
include "simpl2l.mm"
include "simpl2r.mm"
include "simpr.mm"
include "simpl3.mm"
include "cdleme32d.mm"
include "syl131anc.mm"
include "wi.mm"
include "simp11.mm"
include "simp12.mm"
include "simp3.mm"
include "simp2.mm"
include "simp13.mm"
include "cdleme32f.mm"
include "3exp.mm"
include "wceq.mm"
include "simp12l.mm"
include "cdleme31fv2.mm"
include "syl2anc.mm"
include "simp12r.mm"
include "3brtr4d.mm"
include "pm2.61d.mm"
include "imp.mm"
include "pm2.61dan.mm"

theorem cdleme32le
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
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
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let cR: class R
  assume cdleme32.b: |- B = ( Base ` K )
  assume cdleme32.l: |- .<_ = ( le ` K )
  assume cdleme32.j: |- .\/ = ( join ` K )
  assume cdleme32.m: |- ./\ = ( meet ` K )
  assume cdleme32.a: |- A = ( Atoms ` K )
  assume cdleme32.h: |- H = ( LHyp ` K )
  assume cdleme32.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme32.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme32.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme32.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme32.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) )
  assume cdleme32.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )
  assume cdleme32.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme32.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )

  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint D s
  disjoint D y
  disjoint D z
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ x
  disjoint ./\ y
  disjoint ./\ z
  disjoint N x
  disjoint N z
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q x
  disjoint Q y
  disjoint Q z
  disjoint U s
  disjoint U t
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint H y
  disjoint K y
  disjoint Y y
  disjoint H z
  disjoint K z
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint Y z
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint R x
  disjoint R z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( X e. B /\ Y e. B ) /\ X .<_ Y ) -> ( F ` X ) .<_ ( F ` Y ) )

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
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cX
    cY
    c.le
    wbr
    #
    w3a
    #
    cP
    cQ
    wne
    #
    cX
    cW
    c.le
    wbr
    wn
    wa
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.le
    wbr
    #
    @5
    @7
    wa
    @0
    @1
    @2
    @7
    @4
    @10
    @0
    @3
    @4
    @7
    simpl1
    @1
    @2
    @0
    @4
    @7
    simpl2l
    @1
    @2
    @0
    @4
    @7
    simpl2r
    @5
    @7
    simpr
    @0
    @3
    @4
    @7
    simpl3
    vx
    vy
    vz
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
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cX
    cY
    vs
    cdleme32.b
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    cdleme32.u
    cdleme32.c
    cdleme32.d
    cdleme32.e
    cdleme32.i
    cdleme32.n
    cdleme32.o
    cdleme32.f
    cdleme32d
    syl131anc
    @5
    @7
    wn
    #
    @10
    @5
    @6
    cY
    cW
    c.le
    wbr
    wn
    wa
    #
    @11
    @10
    wi
    @5
    @12
    @11
    @10
    @5
    @12
    @11
    w3a
    @0
    @3
    @11
    @12
    @4
    @10
    @0
    @3
    @4
    @12
    @11
    simp11
    @0
    @3
    @4
    @12
    @11
    simp12
    @5
    @12
    @11
    simp3
    @5
    @12
    @11
    simp2
    @0
    @3
    @4
    @12
    @11
    simp13
    vx
    vy
    vz
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
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cX
    cY
    vs
    cdleme32.b
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    cdleme32.u
    cdleme32.c
    cdleme32.d
    cdleme32.e
    cdleme32.i
    cdleme32.n
    cdleme32.o
    cdleme32.f
    cdleme32f
    syl131anc
    3exp
    @5
    @12
    wn
    #
    @11
    @10
    @5
    @13
    @11
    w3a
    #
    cX
    cY
    @8
    @9
    c.le
    @0
    @3
    @4
    @13
    @11
    simp13
    @14
    @1
    @11
    @8
    cX
    wceq
    @1
    @2
    @0
    @4
    @13
    @11
    simp12l
    @5
    @13
    @11
    simp3
    vx
    cB
    cP
    cQ
    cF
    c.le
    cO
    cW
    cX
    cdleme32.f
    cdleme31fv2
    syl2anc
    @14
    @2
    @13
    @9
    cY
    wceq
    @1
    @2
    @0
    @4
    @13
    @11
    simp12r
    @5
    @13
    @11
    simp2
    vx
    cB
    cP
    cQ
    cF
    c.le
    cO
    cW
    cY
    cdleme32.f
    cdleme31fv2
    syl2anc
    3brtr4d
    3exp
    pm2.61d
    imp
    pm2.61dan
end
