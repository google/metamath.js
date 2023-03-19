include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cfv.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "csb.mm"
include "cif.mm"
include "simp2rl.mm"
include "simp2l.mm"
include "simp2rr.mm"
include "jca32.mm"
include "eqid.mm"
include "biid.mm"
include "cvv.mm"
include "vex.mm"
include "cdleme31sc.mm"
include "ax-mp.mm"
include "ifbieq2i.mm"
include "cdleme42b.mm"
include "syld3an2.mm"
include "simp1.mm"
include "simp3l.mm"
include "cdleme32fva1.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eqtr4d.mm"

theorem cdleme48fv
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( X e. B /\ -. X .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( S .\/ ( X ./\ W ) ) = X ) ) -> ( F ` X ) = ( ( F ` S ) .\/ ( X ./\ W ) ) )

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
    #
    cX
    cW
    c.le
    wbr
    wn
    #
    wa
    #
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
    cS
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
    w3a
    #
    cX
    cF
    cfv
    #
    vs
    cS
    vs
    cv
    #
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @15
    @13
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
    #
    vt
    @12
    cD
    csb
    #
    cif
    #
    csb
    #
    @7
    c.or
    co
    #
    cS
    cF
    cfv
    #
    @7
    c.or
    co
    @0
    @2
    @1
    @3
    wa
    wa
    @5
    @9
    @11
    @20
    wceq
    @10
    @2
    @1
    @3
    @2
    @3
    @1
    @0
    @9
    simp2rl
    @0
    @1
    @4
    @9
    simp2l
    #
    @2
    @3
    @1
    @0
    @9
    simp2rr
    jca32
    vx
    vy
    vz
    vt
    cA
    cB
    @12
    cU
    c.or
    co
    cQ
    cP
    @12
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
    cS
    cU
    cD
    cF
    cE
    cH
    @16
    c.or
    cK
    c.le
    c.an
    @18
    @12
    cW
    c.le
    wbr
    wn
    @12
    vx
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    @24
    wceq
    wa
    vz
    cv
    @18
    @25
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
    cX
    vs
    cdlemef46.b
    cdlemef46.l
    cdlemef46.j
    cdlemef46.m
    cdlemef46.a
    cdlemef46.h
    cdlemef46.u
    @23
    eqid
    #
    cdlemef46.d
    cdlemefs46.e
    @16
    eqid
    #
    @14
    @14
    @17
    @23
    @16
    @14
    biid
    @12
    cvv
    wcel
    @17
    @23
    wceq
    vs
    vex
    cvv
    cD
    cP
    cQ
    @12
    cU
    c.or
    c.an
    cW
    @23
    vt
    cdlemef46.d
    @27
    cdleme31sc
    ax-mp
    #
    ifbieq2i
    @26
    eqid
    #
    cdlemef46.f
    cdleme42b
    syld3an2
    @10
    @21
    @19
    @7
    c.or
    @10
    @0
    @6
    @1
    @21
    @19
    wceq
    @0
    @5
    @9
    simp1
    @0
    @5
    @6
    @8
    simp3l
    @22
    vx
    vy
    vz
    vt
    cA
    cB
    @17
    cD
    cP
    cQ
    cS
    cU
    cE
    cF
    cH
    @16
    c.or
    cK
    c.le
    c.an
    @18
    @26
    cW
    vs
    cdlemef46.b
    cdlemef46.l
    cdlemef46.j
    cdlemef46.m
    cdlemef46.a
    cdlemef46.h
    cdlemef46.u
    @29
    cdlemef46.d
    cdlemefs46.e
    @28
    @18
    eqid
    @30
    cdlemef46.f
    cdleme32fva1
    syl3anc
    oveq1d
    eqtr4d
end
