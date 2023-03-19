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
include "wceq.mm"
include "simp1.mm"
include "simp21.mm"
include "simp22.mm"
include "simp3l.mm"
include "cdlemefs32fva1.mm"
include "syl121anc.mm"
include "cdleme43fsv1sn.mm"
include "eqtrd.mm"

theorem cdlemefs31fv1
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
  let cN: class N
  let cO: class O
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  assume cdlemefs32.b: |- B = ( Base ` K )
  assume cdlemefs32.l: |- .<_ = ( le ` K )
  assume cdlemefs32.j: |- .\/ = ( join ` K )
  assume cdlemefs32.m: |- ./\ = ( meet ` K )
  assume cdlemefs32.a: |- A = ( Atoms ` K )
  assume cdlemefs32.h: |- H = ( LHyp ` K )
  assume cdlemefs32.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemefs32.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemefs32.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemefs32.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) )
  assume cdlemefs32.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )
  assume cdleme29fs.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme29fs.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )
  assume cdleme43fsv.y: |- Y = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme43fsv.z: |- Z = ( ( P .\/ Q ) ./\ ( Y .\/ ( ( R .\/ S ) ./\ W ) ) )

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
  disjoint D y
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint H y
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint K y
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
  disjoint P y
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q y
  disjoint Q z
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint U t
  disjoint U y
  disjoint W s
  disjoint W t
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint Y y
  disjoint D s
  disjoint H z
  disjoint K z
  disjoint R z
  disjoint S t
  disjoint S y
  disjoint Z t
  disjoint R x
  disjoint P x
  disjoint Q x
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> ( F ` R ) = Z )

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
    w3a
    #
    cR
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cS
    @5
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cR
    cF
    cfv
    #
    vs
    cR
    cN
    csb
    #
    cZ
    @9
    @0
    @1
    @2
    @6
    @10
    @11
    wceq
    @0
    @4
    @8
    simp1
    @0
    @1
    @2
    @3
    @8
    simp21
    @0
    @1
    @2
    @3
    @8
    simp22
    @0
    @4
    @6
    @7
    simp3l
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
    cdlemefs32.b
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.m
    cdlemefs32.a
    cdlemefs32.h
    cdlemefs32.u
    cdlemefs32.d
    cdlemefs32.e
    cdlemefs32.i
    cdlemefs32.n
    cdleme29fs.o
    cdleme29fs.f
    cdlemefs32fva1
    syl121anc
    vy
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
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
    cY
    cZ
    vs
    cdlemefs32.b
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.m
    cdlemefs32.a
    cdlemefs32.h
    cdlemefs32.u
    cdlemefs32.d
    cdlemefs32.e
    cdlemefs32.i
    cdlemefs32.n
    cdleme43fsv.y
    cdleme43fsv.z
    cdleme43fsv1sn
    eqtrd
end
