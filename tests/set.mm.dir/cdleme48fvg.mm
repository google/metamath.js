include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "simpl3r.mm"
include "simp3ll.mm"
include "adantr.mm"
include "atbase.mm"
include "syl.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "cif.mm"
include "cdleme31id.mm"
include "sylancom.mm"
include "oveq1d.mm"
include "simp2l.mm"
include "sylan.mm"
include "3eqtr4rd.mm"
include "wne.mm"
include "simpl1.mm"
include "simpr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "cdleme48fv.mm"
include "syl121anc.mm"
include "pm2.61dane.mm"

theorem cdleme48fvg
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
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
  let cX: class X
  let vs: setvar s
  let cR: class R
  let ve: setvar e
  assume cdlemef46.b: |- B = ( Base ` K )
  assume cdlemef46.l: |- .<_ = ( le ` K )
  assume cdlemef46.j: |- .\/ = ( join ` K )
  assume cdlemef46.m: |- ./\ = ( meet ` K )
  assume cdlemef46.a: |- A = ( Atoms ` K )
  assume cdlemef46.h: |- H = ( LHyp ` K )
  assume cdlemef46.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemef46.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemefs46.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemef46.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( P .\/ Q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )

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
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint A e
  disjoint F e
  disjoint H e
  disjoint .\/ e
  disjoint K e
  disjoint .<_ e
  disjoint P e
  disjoint Q e
  disjoint W e
  disjoint e s
  disjoint e t
  disjoint e x
  disjoint e y
  disjoint e z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( X e. B /\ -. X .<_ W ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( S .\/ ( X ./\ W ) ) = X ) ) -> ( F ` X ) = ( ( F ` S ) .\/ ( X ./\ W ) ) )

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
    cX
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
    cS
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    w3a
    #
    cX
    cF
    cfv
    #
    cS
    cF
    cfv
    #
    @7
    c.or
    co
    #
    wceq
    #
    cP
    cQ
    @11
    cP
    cQ
    wceq
    #
    wa
    #
    @8
    cX
    @14
    @12
    @6
    @9
    @0
    @3
    @16
    simpl3r
    @17
    @13
    cS
    @7
    c.or
    @11
    @16
    cS
    cB
    wcel
    #
    @13
    cS
    wceq
    @17
    @4
    @18
    @11
    @4
    @16
    @4
    @5
    @9
    @0
    @3
    simp3ll
    adantr
    cA
    cB
    cS
    cK
    cdlemef46.b
    cdlemef46.a
    atbase
    syl
    vx
    cB
    cP
    cQ
    cF
    c.le
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    @19
    vx
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    @20
    wceq
    wa
    vz
    cv
    @19
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @23
    @22
    c.le
    wbr
    wn
    wa
    vy
    cv
    cE
    wceq
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    vt
    @19
    cD
    csb
    cif
    @21
    c.or
    co
    wceq
    wi
    vs
    cA
    wral
    vz
    cB
    crio
    #
    cW
    cS
    cdlemef46.f
    cdleme31id
    sylancom
    oveq1d
    @11
    @1
    @16
    @12
    cX
    wceq
    @0
    @1
    @2
    @10
    simp2l
    vx
    cB
    cP
    cQ
    cF
    c.le
    @24
    cW
    cX
    cdlemef46.f
    cdleme31id
    sylan
    3eqtr4rd
    @11
    cP
    cQ
    wne
    #
    wa
    @0
    @25
    @3
    @10
    @15
    @0
    @3
    @10
    @25
    simpl1
    @11
    @25
    simpr
    @0
    @3
    @10
    @25
    simpl2
    @0
    @3
    @10
    @25
    simpl3
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cP
    cQ
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
    cX
    vs
    cdlemef46.b
    cdlemef46.l
    cdlemef46.j
    cdlemef46.m
    cdlemef46.a
    cdlemef46.h
    cdlemef46.u
    cdlemef46.d
    cdlemefs46.e
    cdlemef46.f
    cdleme48fv
    syl121anc
    pm2.61dane
end
