include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "simplr.mm"
include "atbase.mm"
include "ad2antrl.mm"
include "cdleme31id.mm"
include "sylan.mm"
include "eleq1d.mm"
include "breq1d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "mpbird.mm"
include "wne.mm"
include "csb.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "cdleme32snaw.mm"
include "syl12anc.mm"
include "cdleme32fva1.mm"
include "3expa.mm"
include "pm2.61dane.mm"

theorem cdleme32fvaw
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
  let cR: class R
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
  let vs: setvar s
  let cX: class X
  let cY: class Y
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
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint H y
  disjoint K y
  disjoint R x
  disjoint R z
  disjoint H z
  disjoint K z
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint Y y
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ -. R .<_ W ) ) -> ( ( F ` R ) e. A /\ -. ( F ` R ) .<_ W ) )

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
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    wa
    #
    cR
    cF
    cfv
    #
    cA
    wcel
    #
    @6
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cP
    cQ
    @5
    cP
    cQ
    wceq
    #
    wa
    #
    @10
    @4
    @0
    @4
    @11
    simplr
    @12
    @7
    @1
    @9
    @3
    @12
    @6
    cR
    cA
    @5
    cR
    cB
    wcel
    #
    @11
    @6
    cR
    wceq
    @1
    @13
    @0
    @3
    cA
    cB
    cR
    cK
    cdleme32.b
    cdleme32.a
    atbase
    ad2antrl
    vx
    cB
    cP
    cQ
    cF
    c.le
    cO
    cW
    cR
    cdleme32.f
    cdleme31id
    sylan
    #
    eleq1d
    @12
    @8
    @2
    @12
    @6
    cR
    cW
    c.le
    @14
    breq1d
    notbid
    anbi12d
    mpbird
    @0
    @4
    cP
    cQ
    wne
    #
    @10
    @0
    @4
    @15
    w3a
    #
    @10
    vs
    cR
    cN
    csb
    #
    cA
    wcel
    #
    @17
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @16
    @0
    @15
    @4
    @21
    @0
    @4
    @15
    simp1
    @0
    @4
    @15
    simp3
    @0
    @4
    @15
    simp2
    vy
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cU
    cE
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
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
    cdleme32snaw
    syl12anc
    @16
    @7
    @18
    @9
    @20
    @16
    @6
    @17
    cA
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
    cR
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
    cdleme32fva1
    #
    eleq1d
    @16
    @8
    @19
    @16
    @6
    @17
    cW
    c.le
    @22
    breq1d
    notbid
    anbi12d
    mpbird
    3expa
    pm2.61dane
end
