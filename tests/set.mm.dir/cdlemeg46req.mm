include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "clln.mm"
include "cfv.mm"
include "wceq.mm"
include "simp11l.mm"
include "simp12l.mm"
include "simp13l.mm"
include "simp21.mm"
include "eqid.mm"
include "llni2.mm"
include "syl31anc.mm"
include "simp1.mm"
include "simp23.mm"
include "cdlemeg46fvaw.mm"
include "syl3anc.mm"
include "simpld.mm"
include "simp11.mm"
include "simp22.mm"
include "cdleme46fvaw.mm"
include "syl2anc.mm"
include "simp23l.mm"
include "simp3l.mm"
include "cdleme46fsvlpq.mm"
include "syl121anc.mm"
include "simp3r.mm"
include "nbrne2.mm"
include "lhpat2.mm"
include "syl112anc.mm"
include "clat.mm"
include "hllat.mm"
include "syl.mm"
include "hlatjcl.mm"
include "simp11r.mm"
include "lhpbase.mm"
include "latmle2.mm"
include "syl5eqbr.mm"
include "simprd.mm"
include "necomd.mm"
include "simp22l.mm"
include "hlatlej1.mm"
include "cdlemeg46nlpq.mm"
include "nbrne1.mm"
include "cdlemeg46rgv.mm"
include "wb.mm"
include "atbase.mm"
include "latlem12.mm"
include "syl13anc.mm"
include "mpbi2and.mm"
include "2llnmeqat.mm"
include "syl132anc.mm"

theorem cdlemeg46req
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
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
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume cdlemef46g.b: |- B = ( Base ` K )
  assume cdlemef46g.l: |- .<_ = ( le ` K )
  assume cdlemef46g.j: |- .\/ = ( join ` K )
  assume cdlemef46g.m: |- ./\ = ( meet ` K )
  assume cdlemef46g.a: |- A = ( Atoms ` K )
  assume cdlemef46g.h: |- H = ( LHyp ` K )
  assume cdlemef46g.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemef46g.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemefs46g.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemef46g.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( if ( s .<_ ( P .\/ Q ) , ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) ) , [_ s / t ]_ D ) .\/ ( x ./\ W ) ) ) ) , x ) )
  assume cdlemef46.v: |- V = ( ( Q .\/ P ) ./\ W )
  assume cdlemef46.n: |- N = ( ( v .\/ V ) ./\ ( P .\/ ( ( Q .\/ v ) ./\ W ) ) )
  assume cdlemefs46.o: |- O = ( ( Q .\/ P ) ./\ ( N .\/ ( ( u .\/ v ) ./\ W ) ) )
  assume cdlemef46.g: |- G = ( a e. B |-> if ( ( Q =/= P /\ -. a .<_ W ) , ( iota_ c e. B A. u e. A ( ( -. u .<_ W /\ ( u .\/ ( a ./\ W ) ) = a ) -> c = ( if ( u .<_ ( Q .\/ P ) , ( iota_ b e. B A. v e. A ( ( -. v .<_ W /\ -. v .<_ ( Q .\/ P ) ) -> b = O ) ) , [_ u / v ]_ N ) .\/ ( a ./\ W ) ) ) ) , a ) )
  assume cdlemeg46.y: |- Y = ( ( R .\/ ( G ` S ) ) ./\ W )
  assume cdlemeg46.x: |- X = ( ( ( F ` R ) .\/ S ) ./\ W )

  disjoint s t
  disjoint s x
  disjoint s z
  disjoint Y s
  disjoint t x
  disjoint t z
  disjoint Y t
  disjoint x z
  disjoint Y x
  disjoint Y z
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
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a v
  disjoint A a
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint A b
  disjoint c u
  disjoint c v
  disjoint A c
  disjoint u v
  disjoint A u
  disjoint A v
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B u
  disjoint B v
  disjoint D v
  disjoint G s
  disjoint G t
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H u
  disjoint H v
  disjoint .\/ a
  disjoint .\/ b
  disjoint .\/ c
  disjoint .\/ u
  disjoint .\/ v
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint K u
  disjoint K v
  disjoint .<_ a
  disjoint .<_ b
  disjoint .<_ c
  disjoint .<_ u
  disjoint .<_ v
  disjoint ./\ a
  disjoint ./\ b
  disjoint ./\ c
  disjoint ./\ u
  disjoint ./\ v
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P u
  disjoint P v
  disjoint Q a
  disjoint Q b
  disjoint Q c
  disjoint Q u
  disjoint Q v
  disjoint R a
  disjoint R b
  disjoint R c
  disjoint R u
  disjoint R v
  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S u
  disjoint S v
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint W a
  disjoint W b
  disjoint W c
  disjoint W u
  disjoint W v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint N u
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint O x
  disjoint O y
  disjoint O z
  disjoint t v
  disjoint V u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint V v
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint D a
  disjoint D b
  disjoint D c
  disjoint E a
  disjoint E b
  disjoint E c
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F u
  disjoint F v
  disjoint N t
  disjoint U a
  disjoint U b
  disjoint U c
  disjoint U v
  disjoint V t
  disjoint a s
  disjoint a t
  disjoint b s
  disjoint b t
  disjoint c s
  disjoint c t
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> R = ( ( P .\/ Q ) ./\ ( ( G ` S ) .\/ X ) ) )

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
    @18
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    @0
    @18
    cK
    clln
    cfv
    #
    wcel
    #
    cS
    cG
    cfv
    #
    cX
    c.or
    co
    #
    @23
    wcel
    #
    @11
    @18
    @26
    wne
    cR
    @18
    @26
    c.an
    co
    #
    c.le
    wbr
    #
    cR
    @28
    wceq
    @0
    @1
    @5
    @8
    @17
    @21
    simp11l
    #
    @22
    @0
    @3
    @6
    @10
    @24
    @30
    @3
    @4
    @2
    @8
    @17
    @21
    simp12l
    #
    @6
    @7
    @2
    @5
    @17
    @21
    simp13l
    #
    @9
    @10
    @13
    @16
    @21
    simp21
    #
    cA
    cP
    cQ
    c.or
    cK
    @23
    cdlemef46g.j
    cdlemef46g.a
    @23
    eqid
    #
    llni2
    syl31anc
    @22
    @0
    @25
    cA
    wcel
    #
    cX
    cA
    wcel
    #
    @25
    cX
    wne
    @27
    @30
    @22
    @35
    @25
    cW
    c.le
    wbr
    wn
    #
    @22
    @9
    @16
    @10
    @35
    @37
    wa
    @9
    @17
    @21
    simp1
    #
    @9
    @10
    @13
    @16
    @21
    simp23
    #
    @33
    vx
    vy
    vz
    vv
    vu
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
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cV
    cW
    vs
    va
    vb
    vc
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    cdlemef46g.d
    cdlemefs46g.e
    cdlemef46g.f
    cdlemef46.v
    cdlemef46.n
    cdlemefs46.o
    cdlemef46.g
    cdlemeg46fvaw
    syl3anc
    #
    simpld
    #
    @22
    @2
    cR
    cF
    cfv
    #
    cA
    wcel
    #
    @42
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    @14
    @42
    cS
    wne
    #
    @36
    @2
    @5
    @8
    @17
    @21
    simp11
    @22
    @9
    @13
    @45
    @38
    @9
    @10
    @13
    @16
    @21
    simp22
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
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    cdlemef46g.d
    cdlemefs46g.e
    cdlemef46g.f
    cdleme46fvaw
    syl2anc
    #
    @14
    @15
    @10
    @13
    @9
    @21
    simp23l
    #
    @22
    @42
    @18
    c.le
    wbr
    #
    @20
    @46
    @22
    @9
    @10
    @13
    @19
    @50
    @38
    @33
    @47
    @9
    @17
    @19
    @20
    simp3l
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
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    cdlemef46g.d
    cdlemefs46g.e
    cdlemef46g.f
    cdleme46fsvlpq
    syl121anc
    @9
    @17
    @19
    @20
    simp3r
    #
    @42
    cS
    @18
    c.le
    nbrne2
    syl2anc
    cA
    @42
    cS
    cX
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemeg46.x
    lhpat2
    syl112anc
    #
    @22
    cX
    @25
    @22
    cX
    cW
    c.le
    wbr
    @37
    cX
    @25
    wne
    @22
    cX
    @42
    cS
    c.or
    co
    #
    cW
    c.an
    co
    #
    cW
    c.le
    cdlemeg46.x
    @22
    cK
    clat
    wcel
    #
    @54
    cB
    wcel
    #
    cW
    cB
    wcel
    #
    @55
    cW
    c.le
    wbr
    @22
    @0
    @56
    @30
    cK
    hllat
    syl
    #
    @22
    @0
    @43
    @14
    @57
    @30
    @22
    @43
    @44
    @48
    simpld
    @49
    cA
    cB
    c.or
    cK
    @42
    cS
    cdlemef46g.b
    cdlemef46g.j
    cdlemef46g.a
    hlatjcl
    syl3anc
    @22
    @1
    @58
    @0
    @1
    @5
    @8
    @17
    @21
    simp11r
    cB
    cH
    cK
    cW
    cdlemef46g.b
    cdlemef46g.h
    lhpbase
    syl
    cB
    cK
    c.le
    c.an
    @54
    cW
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.m
    latmle2
    syl3anc
    syl5eqbr
    @22
    @35
    @37
    @40
    simprd
    cX
    @25
    cW
    c.le
    nbrne2
    syl2anc
    necomd
    cA
    @25
    cX
    c.or
    cK
    @23
    cdlemef46g.j
    cdlemef46g.a
    @34
    llni2
    syl31anc
    @11
    @12
    @10
    @16
    @9
    @21
    simp22l
    #
    @22
    @26
    @18
    @22
    @25
    @26
    c.le
    wbr
    #
    @25
    @18
    c.le
    wbr
    wn
    #
    @26
    @18
    wne
    @22
    @0
    @35
    @36
    @61
    @30
    @41
    @53
    cA
    @25
    cX
    c.or
    cK
    c.le
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.a
    hlatlej1
    syl3anc
    @22
    @9
    @10
    @16
    @20
    @62
    @38
    @33
    @39
    @52
    vx
    vy
    vz
    vv
    vu
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
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cV
    cW
    vs
    va
    vb
    vc
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    cdlemef46g.d
    cdlemefs46g.e
    cdlemef46g.f
    cdlemef46.v
    cdlemef46.n
    cdlemefs46.o
    cdlemef46.g
    cdlemeg46nlpq
    syl121anc
    @25
    @26
    @18
    c.le
    nbrne1
    syl2anc
    necomd
    @22
    @19
    cR
    @26
    c.le
    wbr
    #
    @29
    @51
    vx
    vy
    vz
    vv
    vu
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
    cG
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cV
    cW
    cX
    cY
    vs
    va
    vb
    vc
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.j
    cdlemef46g.m
    cdlemef46g.a
    cdlemef46g.h
    cdlemef46g.u
    cdlemef46g.d
    cdlemefs46g.e
    cdlemef46g.f
    cdlemef46.v
    cdlemef46.n
    cdlemefs46.o
    cdlemef46.g
    cdlemeg46.y
    cdlemeg46.x
    cdlemeg46rgv
    @22
    @56
    cR
    cB
    wcel
    #
    @18
    cB
    wcel
    #
    @26
    cB
    wcel
    #
    @19
    @63
    wa
    @29
    wb
    @59
    @22
    @11
    @64
    @60
    cA
    cB
    cR
    cK
    cdlemef46g.b
    cdlemef46g.a
    atbase
    syl
    @22
    @0
    @3
    @6
    @65
    @30
    @31
    @32
    cA
    cB
    c.or
    cK
    cP
    cQ
    cdlemef46g.b
    cdlemef46g.j
    cdlemef46g.a
    hlatjcl
    syl3anc
    @22
    @0
    @35
    @36
    @66
    @30
    @41
    @53
    cA
    cB
    c.or
    cK
    @25
    cX
    cdlemef46g.b
    cdlemef46g.j
    cdlemef46g.a
    hlatjcl
    syl3anc
    cB
    cK
    c.le
    c.an
    cR
    @18
    @26
    cdlemef46g.b
    cdlemef46g.l
    cdlemef46g.m
    latlem12
    syl13anc
    mpbi2and
    cA
    cR
    cK
    c.le
    c.an
    @23
    @18
    @26
    cdlemef46g.l
    cdlemef46g.m
    cdlemef46g.a
    @34
    2llnmeqat
    syl132anc
end
