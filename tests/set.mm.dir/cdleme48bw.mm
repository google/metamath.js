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
include "simp1.mm"
include "simp3l.mm"
include "cdleme46fvaw.mm"
include "syl2anc.mm"
include "simprd.mm"
include "clat.mm"
include "simp11l.mm"
include "hllat.mm"
include "syl.mm"
include "simpld.mm"
include "atbase.mm"
include "simp2rl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmcl.mm"
include "syl3anc.mm"
include "latlej1.mm"
include "cdleme48fv.mm"
include "breqtrrd.mm"
include "wi.mm"
include "cv.mm"
include "csb.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "cvv.mm"
include "vex.mm"
include "eqid.mm"
include "cdleme31sc.mm"
include "ax-mp.mm"
include "cdleme32fvcl.mm"
include "lattr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "mtod.mm"

theorem cdleme48bw
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( X e. B /\ -. X .<_ W ) ) /\ ( ( S e. A /\ -. S .<_ W ) /\ ( S .\/ ( X ./\ W ) ) = X ) ) -> -. ( F ` X ) .<_ W )

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
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
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
    cW
    c.le
    wbr
    #
    cS
    cF
    cfv
    #
    cW
    c.le
    wbr
    #
    @13
    @16
    cA
    wcel
    #
    @17
    wn
    #
    @13
    @4
    @9
    @18
    @19
    wa
    @4
    @8
    @12
    simp1
    #
    @4
    @8
    @9
    @11
    simp3l
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
    cdleme46fvaw
    syl2anc
    #
    simprd
    @13
    @16
    @14
    c.le
    wbr
    #
    @15
    @17
    @13
    @16
    @16
    @10
    c.or
    co
    #
    @14
    c.le
    @13
    cK
    clat
    wcel
    #
    @16
    cB
    wcel
    #
    @10
    cB
    wcel
    #
    @16
    @23
    c.le
    wbr
    @13
    @0
    @24
    @0
    @1
    @2
    @3
    @8
    @12
    simp11l
    cK
    hllat
    syl
    #
    @13
    @18
    @25
    @13
    @18
    @19
    @21
    simpld
    cA
    cB
    @16
    cK
    cdlemef46.b
    cdlemef46.a
    atbase
    syl
    #
    @13
    @24
    @6
    cW
    cB
    wcel
    #
    @26
    @27
    @6
    @7
    @5
    @4
    @12
    simp2rl
    #
    @13
    @1
    @29
    @0
    @1
    @2
    @3
    @8
    @12
    simp11r
    cB
    cH
    cK
    cW
    cdlemef46.b
    cdlemef46.h
    lhpbase
    syl
    #
    cB
    cK
    c.an
    cX
    cW
    cdlemef46.b
    cdlemef46.m
    latmcl
    syl3anc
    cB
    c.or
    cK
    c.le
    @16
    @10
    cdlemef46.b
    cdlemef46.l
    cdlemef46.j
    latlej1
    syl3anc
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
    breqtrrd
    @13
    @24
    @25
    @14
    cB
    wcel
    #
    @29
    @22
    @15
    wa
    @17
    wi
    @27
    @28
    @13
    @4
    @6
    @32
    @20
    @30
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
    cU
    cE
    cF
    cH
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @35
    cP
    cQ
    c.or
    co
    #
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
    c.or
    cK
    c.le
    c.an
    @33
    @36
    c.le
    wbr
    @37
    @34
    cif
    #
    @33
    cW
    c.le
    wbr
    wn
    @33
    vx
    cv
    #
    cW
    c.an
    co
    #
    c.or
    co
    @39
    wceq
    wa
    vz
    cv
    @38
    @40
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
    @33
    cvv
    wcel
    @34
    @33
    cU
    c.or
    co
    cQ
    cP
    @33
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
    wceq
    vs
    vex
    cvv
    cD
    cP
    cQ
    @33
    cU
    c.or
    c.an
    cW
    @42
    vt
    cdlemef46.d
    @42
    eqid
    cdleme31sc
    ax-mp
    cdlemef46.d
    cdlemefs46.e
    @37
    eqid
    @38
    eqid
    @41
    eqid
    cdlemef46.f
    cdleme32fvcl
    syl2anc
    @31
    cB
    cK
    c.le
    @16
    @14
    cW
    cdlemef46.b
    cdlemef46.l
    lattr
    syl13anc
    mpand
    mtod
end
