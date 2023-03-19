include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cfv.mm"
include "csb.mm"
include "cv.mm"
include "cif.mm"
include "eqid.mm"
include "cdlemefs31fv1.mm"
include "wceq.mm"
include "simp22l.mm"
include "simp23l.mm"
include "cdleme31sde.mm"
include "syl2anc.mm"
include "eqtr4d.mm"

theorem cdlemefs44
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cO: class O
  let cW: class W
  let vs: setvar s
  assume cdlemef44.b: |- B = ( Base ` K )
  assume cdlemef44.l: |- .<_ = ( le ` K )
  assume cdlemef44.j: |- .\/ = ( join ` K )
  assume cdlemef44.m: |- ./\ = ( meet ` K )
  assume cdlemef44.a: |- A = ( Atoms ` K )
  assume cdlemef44.h: |- H = ( LHyp ` K )
  assume cdlemef44.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemef44.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemef44.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( P .\/ Q ) , I , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) )
  assume cdlemef44.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )
  assume cdlemefs44.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemefs44.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) )

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
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint I x
  disjoint I z
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  disjoint K z
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
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  disjoint R z
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
  disjoint D s
  disjoint S s
  disjoint S t
  disjoint S y
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> ( F ` R ) = [_ R / s ]_ [_ S / t ]_ E )

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
    w3a
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    cS
    @8
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cR
    cF
    cfv
    @8
    cS
    cU
    c.or
    co
    cQ
    cP
    cS
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    cR
    cS
    c.or
    co
    cW
    c.an
    co
    c.or
    co
    c.an
    co
    #
    vs
    cR
    vt
    cS
    cE
    csb
    csb
    #
    vx
    vy
    vz
    vt
    cA
    cB
    vt
    vs
    cv
    #
    cD
    csb
    #
    cD
    cP
    cQ
    cR
    cS
    cU
    cE
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    @14
    @8
    c.le
    wbr
    cI
    @15
    cif
    #
    cO
    cW
    @11
    @12
    vs
    cdlemef44.b
    cdlemef44.l
    cdlemef44.j
    cdlemef44.m
    cdlemef44.a
    cdlemef44.h
    cdlemef44.u
    cdlemef44.d
    cdlemefs44.e
    cdlemefs44.i
    @16
    eqid
    cdlemef44.o
    cdlemef44.f
    @11
    eqid
    #
    @12
    eqid
    #
    cdlemefs31fv1
    @10
    @2
    @5
    @13
    @12
    wceq
    @2
    @3
    @1
    @7
    @0
    @9
    simp22l
    @5
    @6
    @1
    @4
    @0
    @9
    simp23l
    vt
    cA
    cD
    cP
    cQ
    cR
    cS
    cU
    cE
    c.or
    c.an
    cW
    @11
    @12
    vs
    cdlemef44.d
    cdlemefs44.e
    @17
    @18
    cdleme31sde
    syl2anc
    eqtr4d
end
