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
include "simp2l.mm"
include "simp12.mm"
include "simp2r.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "hlatlej1.mm"
include "syl3anc.mm"
include "simp3.mm"
include "cdlemefs45.mm"
include "syl132anc.mm"
include "simp2rl.mm"
include "eqid.mm"
include "cdleme31sde.mm"
include "syl2anc.mm"
include "simp11.mm"
include "cdleme17d1.mm"
include "syl131anc.mm"
include "3eqtrd.mm"

theorem cdleme17d2
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
  let vs: setvar s
  let cR: class R
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
  disjoint R s
  disjoint R t
  disjoint R x
  disjoint R y
  disjoint R z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( S e. A /\ -. S .<_ W ) ) /\ -. S .<_ ( P .\/ Q ) ) -> ( F ` P ) = Q )

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
    w3a
    #
    cP
    cQ
    wne
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
    wa
    #
    cS
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
    cP
    cF
    cfv
    #
    vs
    cP
    vt
    cS
    cE
    csb
    csb
    #
    @15
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
    #
    c.or
    co
    c.an
    co
    #
    @20
    c.or
    co
    c.an
    co
    #
    cQ
    @17
    @9
    @10
    @5
    @13
    cP
    @15
    c.le
    wbr
    #
    @16
    @18
    @19
    wceq
    @9
    @14
    @16
    simp1
    @9
    @10
    @13
    @16
    simp2l
    @2
    @5
    @8
    @14
    @16
    simp12
    #
    @9
    @10
    @13
    @16
    simp2r
    #
    @17
    @0
    @3
    @6
    @23
    @0
    @1
    @5
    @8
    @14
    @16
    simp11l
    @3
    @4
    @2
    @8
    @14
    @16
    simp12l
    #
    @6
    @7
    @2
    @5
    @14
    @16
    simp13l
    #
    cA
    cP
    cQ
    c.or
    cK
    c.le
    cdlemef46.l
    cdlemef46.j
    cdlemef46.a
    hlatlej1
    syl3anc
    @9
    @14
    @16
    simp3
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
    cP
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
    cdlemef46.b
    cdlemef46.l
    cdlemef46.j
    cdlemef46.m
    cdlemef46.a
    cdlemef46.h
    cdlemef46.u
    cdlemef46.d
    cdlemef46.f
    cdlemefs46.e
    cdlemefs45
    syl132anc
    @17
    @3
    @11
    @19
    @22
    wceq
    @26
    @11
    @12
    @10
    @9
    @16
    simp2rl
    vt
    cA
    cD
    cP
    cQ
    cP
    cS
    cU
    cE
    c.or
    c.an
    cW
    @21
    @22
    vs
    cdlemef46.d
    cdlemefs46.e
    @21
    eqid
    #
    @22
    eqid
    #
    cdleme31sde
    syl2anc
    @17
    @2
    @5
    @6
    @13
    @16
    @22
    cQ
    wceq
    @2
    @5
    @8
    @14
    @16
    simp11
    @24
    @27
    @25
    @28
    cA
    cP
    cQ
    cS
    cU
    @21
    @22
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemef46.l
    cdlemef46.j
    cdlemef46.m
    cdlemef46.a
    cdlemef46.h
    cdlemef46.u
    @29
    @30
    cdleme17d1
    syl131anc
    3eqtrd
end
