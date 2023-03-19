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
include "cdlemefs45.mm"
include "wceq.mm"
include "simp22l.mm"
include "simp23l.mm"
include "eqid.mm"
include "cdleme31sde.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem cdlemefs45ee
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
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vs: setvar s
  assume cdlemef45.b: |- B = ( Base ` K )
  assume cdlemef45.l: |- .<_ = ( le ` K )
  assume cdlemef45.j: |- .\/ = ( join ` K )
  assume cdlemef45.m: |- ./\ = ( meet ` K )
  assume cdlemef45.a: |- A = ( Atoms ` K )
  assume cdlemef45.h: |- H = ( LHyp ` K )
  assume cdlemef45.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemef45.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemef45.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( P .\/ Q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )
  assume cdlemefs45.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )

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
  disjoint D s
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint H s
  disjoint H t
  disjoint H x
  disjoint H y
  disjoint H z
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
  disjoint S s
  disjoint S t
  disjoint S y
  disjoint S x
  disjoint S z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> ( F ` R ) = ( ( P .\/ Q ) ./\ ( ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) ) .\/ ( ( R .\/ S ) ./\ W ) ) ) )

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
    vs
    cR
    vt
    cS
    cE
    csb
    csb
    #
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
    vx
    vy
    vz
    vt
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
    cW
    vs
    cdlemef45.b
    cdlemef45.l
    cdlemef45.j
    cdlemef45.m
    cdlemef45.a
    cdlemef45.h
    cdlemef45.u
    cdlemef45.d
    cdlemef45.f
    cdlemefs45.e
    cdlemefs45
    @10
    @2
    @5
    @11
    @13
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
    @12
    @13
    vs
    cdlemef45.d
    cdlemefs45.e
    @12
    eqid
    @13
    eqid
    cdleme31sde
    syl2anc
    eqtrd
end
