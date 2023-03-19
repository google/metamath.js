include "csb.mm"
include "wceq.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wbr.mm"
include "cif.mm"
include "breq1.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "eqeq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "3eqtr4g.mm"
include "syl6eqr.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "cbvriotav.mm"
include "syl6eq.mm"
include "ifbieq12d.mm"
include "cbvcsbv.mm"
include "a1i.mm"

theorem cdleme40v
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
  let cT: class T
  let cU: class U
  let cE: class E
  let cG: class G
  let cH: class H
  let cI: class I
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
  let cF: class F
  let cS: class S
  assume cdleme40.b: |- B = ( Base ` K )
  assume cdleme40.l: |- .<_ = ( le ` K )
  assume cdleme40.j: |- .\/ = ( join ` K )
  assume cdleme40.m: |- ./\ = ( meet ` K )
  assume cdleme40.a: |- A = ( Atoms ` K )
  assume cdleme40.h: |- H = ( LHyp ` K )
  assume cdleme40.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme40.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme40.g: |- G = ( ( P .\/ Q ) ./\ ( E .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme40.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = G ) )
  assume cdleme40.n: |- N = if ( s .<_ ( P .\/ Q ) , I , D )
  assume cdleme40.d: |- D = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme40r.y: |- Y = ( ( u .\/ U ) ./\ ( Q .\/ ( ( P .\/ u ) ./\ W ) ) )
  assume cdleme40r.t: |- T = ( ( v .\/ U ) ./\ ( Q .\/ ( ( P .\/ v ) ./\ W ) ) )
  assume cdleme40r.x: |- X = ( ( P .\/ Q ) ./\ ( T .\/ ( ( u .\/ v ) ./\ W ) ) )
  assume cdleme40r.o: |- O = ( iota_ z e. B A. v e. A ( ( -. v .<_ W /\ -. v .<_ ( P .\/ Q ) ) -> z = X ) )
  assume cdleme40r.v: |- V = if ( u .<_ ( P .\/ Q ) , O , Y )

  disjoint v z
  disjoint E v
  disjoint E z
  disjoint u v
  disjoint N u
  disjoint N v
  disjoint R u
  disjoint V s
  disjoint t y
  disjoint X t
  disjoint X y
  disjoint s t
  disjoint s u
  disjoint s y
  disjoint s z
  disjoint t u
  disjoint t z
  disjoint u y
  disjoint u z
  disjoint y z
  disjoint u v
  disjoint u z
  disjoint A u
  disjoint v z
  disjoint A v
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B z
  disjoint H v
  disjoint H z
  disjoint .\/ u
  disjoint .\/ v
  disjoint .\/ z
  disjoint K v
  disjoint K z
  disjoint .<_ u
  disjoint .<_ v
  disjoint .<_ z
  disjoint ./\ u
  disjoint ./\ v
  disjoint ./\ z
  disjoint P u
  disjoint P v
  disjoint P z
  disjoint Q u
  disjoint Q v
  disjoint Q z
  disjoint R v
  disjoint R z
  disjoint T u
  disjoint U v
  disjoint U z
  disjoint W u
  disjoint W v
  disjoint W z
  disjoint s v
  disjoint s t
  disjoint s y
  disjoint A s
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint B s
  disjoint B t
  disjoint B y
  disjoint E s
  disjoint H t
  disjoint H y
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ y
  disjoint K t
  disjoint K y
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ y
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ y
  disjoint P s
  disjoint P t
  disjoint P y
  disjoint Q s
  disjoint Q t
  disjoint Q y
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint U t
  disjoint U y
  disjoint W s
  disjoint W t
  disjoint W y
  disjoint Y y
  disjoint t v
  disjoint v y
  disjoint T s
  disjoint T t
  disjoint T y
  disjoint F z
  disjoint S u
  disjoint S z
  disjoint F t
  disjoint S t
  disjoint S v
  disjoint S y
  assert |- ( R e. A -> [_ R / s ]_ N = [_ R / u ]_ V )

  proof
    vs
    cR
    cN
    csb
    vu
    cR
    cV
    csb
    wceq
    cR
    cA
    wcel
    vs
    vu
    cR
    cN
    cV
    vs
    cv
    #
    vu
    cv
    #
    wceq
    #
    @0
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cI
    cD
    cif
    @1
    @3
    c.le
    wbr
    #
    cO
    cY
    cif
    cN
    cV
    @2
    @4
    @5
    cI
    cD
    cO
    cY
    @0
    @1
    @3
    c.le
    breq1
    @2
    vt
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @6
    @3
    c.le
    wbr
    #
    wn
    #
    wa
    #
    vy
    cv
    #
    cG
    wceq
    #
    wi
    #
    vt
    cA
    wral
    #
    vy
    cB
    crio
    #
    vv
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @17
    @3
    c.le
    wbr
    #
    wn
    #
    wa
    #
    vz
    cv
    #
    cX
    wceq
    #
    wi
    #
    vv
    cA
    wral
    #
    vz
    cB
    crio
    #
    cI
    cO
    @2
    @16
    @11
    @12
    @3
    cE
    @1
    @6
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    #
    wceq
    #
    wi
    #
    vt
    cA
    wral
    #
    vy
    cB
    crio
    @27
    @2
    @15
    @34
    vy
    cB
    @2
    @14
    @33
    vt
    cA
    @2
    @13
    @32
    @11
    @2
    cG
    @31
    @12
    @2
    cG
    @3
    cE
    @0
    @6
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    @31
    cdleme40.g
    @2
    @37
    @30
    @3
    c.an
    @2
    @36
    @29
    cE
    c.or
    @2
    @35
    @28
    cW
    c.an
    @0
    @1
    @6
    c.or
    oveq1
    oveq1d
    oveq2d
    oveq2d
    syl5eq
    eqeq2d
    imbi2d
    ralbidv
    riotabidv
    @34
    @26
    vy
    vz
    cB
    @12
    @23
    wceq
    #
    @34
    @11
    @23
    @31
    wceq
    #
    wi
    #
    vt
    cA
    wral
    @26
    @38
    @33
    @40
    vt
    cA
    @38
    @32
    @39
    @11
    @12
    @23
    @31
    eqeq1
    imbi2d
    ralbidv
    @40
    @25
    vt
    vv
    cA
    @6
    @17
    wceq
    #
    @11
    @22
    @39
    @24
    @41
    @8
    @19
    @10
    @21
    @41
    @7
    @18
    @6
    @17
    cW
    c.le
    breq1
    notbid
    @41
    @9
    @20
    @6
    @17
    @3
    c.le
    breq1
    notbid
    anbi12d
    @41
    @31
    cX
    @23
    @41
    @31
    @3
    cT
    @1
    @17
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cX
    @41
    @30
    @44
    @3
    c.an
    @41
    cE
    cT
    @29
    @43
    c.or
    @41
    @6
    cU
    c.or
    co
    #
    cQ
    cP
    @6
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    @17
    cU
    c.or
    co
    #
    cQ
    cP
    @17
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cE
    cT
    @41
    @45
    @49
    @48
    @52
    c.an
    @6
    @17
    cU
    c.or
    oveq1
    @41
    @47
    @51
    cQ
    c.or
    @41
    @46
    @50
    cW
    c.an
    @6
    @17
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    cdleme40.e
    cdleme40r.t
    3eqtr4g
    @41
    @28
    @42
    cW
    c.an
    @6
    @17
    @1
    c.or
    oveq2
    oveq1d
    oveq12d
    oveq2d
    cdleme40r.x
    syl6eqr
    eqeq2d
    imbi12d
    cbvralv
    syl6bb
    cbvriotav
    syl6eq
    cdleme40.i
    cdleme40r.o
    3eqtr4g
    @2
    @0
    cU
    c.or
    co
    #
    cQ
    cP
    @0
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    @1
    cU
    c.or
    co
    #
    cQ
    cP
    @1
    c.or
    co
    #
    cW
    c.an
    co
    #
    c.or
    co
    #
    c.an
    co
    cD
    cY
    @2
    @53
    @57
    @56
    @60
    c.an
    @0
    @1
    cU
    c.or
    oveq1
    @2
    @55
    @59
    cQ
    c.or
    @2
    @54
    @58
    cW
    c.an
    @0
    @1
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    cdleme40.d
    cdleme40r.y
    3eqtr4g
    ifbieq12d
    cdleme40.n
    cdleme40r.v
    3eqtr4g
    cbvcsbv
    a1i
end
