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
include "biid.mm"
include "cvv.mm"
include "wceq.mm"
include "vex.mm"
include "cdleme31sc.mm"
include "ax-mp.mm"
include "ifbieq2i.mm"
include "cdlemefr31fv1.mm"
include "simp2rl.mm"
include "syl.mm"
include "eqtr4d.mm"

theorem cdlemefr44
  let vx: setvar x
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
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
  let vy: setvar y
  let cE: class E
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

  disjoint s t
  disjoint s x
  disjoint s z
  disjoint A s
  disjoint t x
  disjoint t z
  disjoint A t
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B x
  disjoint B z
  disjoint D x
  disjoint D z
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint H z
  disjoint I x
  disjoint I z
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K z
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ x
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ x
  disjoint ./\ z
  disjoint P s
  disjoint P t
  disjoint P x
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q x
  disjoint Q z
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R z
  disjoint U s
  disjoint U t
  disjoint U x
  disjoint U z
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W z
  disjoint s y
  disjoint t y
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint B y
  disjoint D y
  disjoint E y
  disjoint H y
  disjoint .\/ y
  disjoint K y
  disjoint .<_ y
  disjoint ./\ y
  disjoint P y
  disjoint Q y
  disjoint R y
  disjoint U y
  disjoint W y
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ -. R .<_ ( P .\/ Q ) ) -> ( F ` R ) = [_ R / t ]_ D )

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
    wa
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    wn
    #
    w3a
    #
    cR
    cF
    cfv
    cR
    cU
    c.or
    co
    cQ
    cP
    cR
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
    vt
    cR
    cD
    csb
    #
    vx
    vz
    cA
    cB
    vs
    cv
    #
    cU
    c.or
    co
    cQ
    cP
    @9
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
    cP
    cQ
    cR
    cU
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    @9
    @4
    c.le
    wbr
    #
    cI
    vt
    @9
    cD
    csb
    #
    cif
    cO
    cW
    @7
    vs
    cdlemef44.b
    cdlemef44.l
    cdlemef44.j
    cdlemef44.m
    cdlemef44.a
    cdlemef44.h
    cdlemef44.u
    @10
    eqid
    #
    @11
    @11
    @12
    @10
    cI
    @11
    biid
    @9
    cvv
    wcel
    @12
    @10
    wceq
    vs
    vex
    cvv
    cD
    cP
    cQ
    @9
    cU
    c.or
    c.an
    cW
    @10
    vt
    cdlemef44.d
    @13
    cdleme31sc
    ax-mp
    ifbieq2i
    cdlemef44.o
    cdlemef44.f
    @7
    eqid
    #
    cdlemefr31fv1
    @6
    @2
    @8
    @7
    wceq
    @2
    @3
    @1
    @0
    @5
    simp2rl
    cA
    cD
    cP
    cQ
    cR
    cU
    c.or
    c.an
    cW
    @7
    vt
    cdlemef44.d
    @14
    cdleme31sc
    syl
    eqtr4d
end
