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
include "cfv.mm"
include "cvv.mm"
include "wi.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "anass.mm"
include "wral.mm"
include "crio.mm"
include "eqid.mm"
include "cdleme31fv1.mm"
include "adantl.mm"
include "cdleme32fvcl.mm"
include "adantrr.mm"
include "riotasvd.mm"
include "syl5bi.mm"
include "mpan2.mm"
include "3impia.mm"

theorem cdleme32a
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
  let vs: setvar s
  let cR: class R
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
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint H y
  disjoint K y
  disjoint H z
  disjoint K z
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint Y y
  disjoint R x
  disjoint R z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( X e. B /\ ( P =/= Q /\ -. X .<_ W ) ) /\ ( ( s e. A /\ -. s .<_ W ) /\ ( s .\/ ( X ./\ W ) ) = X ) ) -> ( F ` X ) = ( N .\/ ( X ./\ W ) ) )

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
    cP
    cQ
    wne
    cX
    cW
    c.le
    wbr
    wn
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
    @4
    cW
    c.le
    wbr
    wn
    #
    wa
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
    cX
    cF
    cfv
    #
    cN
    @7
    c.or
    co
    #
    wceq
    #
    @0
    @3
    wa
    #
    cB
    cvv
    wcel
    #
    @9
    @12
    wi
    cB
    cK
    cbs
    cfv
    cvv
    cdleme32.b
    cK
    cbs
    fvex
    eqeltri
    @9
    @5
    @6
    @8
    wa
    #
    wa
    @13
    @14
    wa
    @12
    @5
    @6
    @8
    anass
    @13
    @15
    vz
    vs
    cB
    cA
    @11
    @10
    cvv
    @3
    @10
    @15
    vz
    cv
    @11
    wceq
    wi
    vs
    cA
    wral
    vz
    cB
    crio
    #
    wceq
    @0
    vx
    vz
    cA
    cB
    @16
    cP
    cQ
    cF
    c.or
    c.le
    c.an
    cN
    cO
    cW
    cX
    vs
    cdleme32.o
    cdleme32.f
    @16
    eqid
    cdleme31fv1
    adantl
    @0
    @1
    @10
    cB
    wcel
    @2
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
    cdleme32fvcl
    adantrr
    riotasvd
    syl5bi
    mpan2
    3impia
end
