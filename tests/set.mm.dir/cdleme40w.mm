include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "csb.mm"
include "cv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "eqid.mm"
include "cdleme40n.mm"
include "simp23l.mm"
include "cdleme40v.mm"
include "syl.mm"
include "neeqtrrd.mm"

theorem cdleme40w
  let vy: setvar y
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
  let cG: class G
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cY: class Y
  let vs: setvar s
  let vv: setvar v
  let vz: setvar z
  let cF: class F
  let cT: class T
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

  disjoint A u
  disjoint B u
  disjoint .\/ u
  disjoint .<_ u
  disjoint ./\ u
  disjoint P u
  disjoint Q u
  disjoint S u
  disjoint W u
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
  disjoint S t
  disjoint S y
  disjoint E y
  disjoint N u
  disjoint S s
  disjoint s u
  disjoint U s
  disjoint U u
  disjoint t u
  disjoint u y
  disjoint u v
  disjoint u z
  disjoint v z
  disjoint A v
  disjoint A z
  disjoint B v
  disjoint B z
  disjoint F z
  disjoint H v
  disjoint H z
  disjoint .\/ v
  disjoint .\/ z
  disjoint K v
  disjoint K z
  disjoint .<_ v
  disjoint .<_ z
  disjoint ./\ v
  disjoint ./\ z
  disjoint P v
  disjoint P z
  disjoint Q v
  disjoint Q z
  disjoint R v
  disjoint R z
  disjoint S z
  disjoint T u
  disjoint U v
  disjoint U z
  disjoint W v
  disjoint W z
  disjoint s v
  disjoint F t
  disjoint t v
  disjoint S v
  disjoint v y
  disjoint T s
  disjoint T t
  disjoint T y
  disjoint D v
  disjoint E v
  disjoint y z
  disjoint E z
  disjoint I v
  disjoint N v
  disjoint s z
  disjoint t z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ S .<_ ( P .\/ Q ) /\ R =/= S ) ) -> [_ R / s ]_ N =/= [_ S / s ]_ N )

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
    #
    cS
    cW
    c.le
    wbr
    wn
    #
    wa
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
    @5
    c.le
    wbr
    cR
    cS
    wne
    w3a
    #
    w3a
    #
    vs
    cR
    cN
    csb
    vu
    cS
    vu
    cv
    #
    @5
    c.le
    wbr
    vv
    cv
    #
    cW
    c.le
    wbr
    wn
    @9
    @5
    c.le
    wbr
    wn
    wa
    #
    vz
    cv
    #
    @5
    @9
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
    @8
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
    wceq
    wi
    vv
    cA
    wral
    vz
    cB
    crio
    #
    @8
    cU
    c.or
    co
    cQ
    cP
    @8
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
    cif
    #
    csb
    #
    vs
    cS
    cN
    csb
    #
    vy
    vz
    vv
    vu
    vt
    cA
    cB
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @19
    @5
    c.le
    wbr
    wn
    wa
    vy
    cv
    @5
    cE
    cR
    @19
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
    wi
    vt
    cA
    wral
    vy
    cB
    crio
    #
    cD
    cP
    cQ
    cR
    cS
    @15
    @12
    cU
    cE
    @5
    @12
    cS
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
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    @14
    @16
    cW
    @13
    @20
    @10
    @11
    @22
    wceq
    wi
    vv
    cA
    wral
    vz
    cB
    crio
    #
    vs
    cdleme40.b
    cdleme40.l
    cdleme40.j
    cdleme40.m
    cdleme40.a
    cdleme40.h
    cdleme40.u
    cdleme40.e
    cdleme40.g
    cdleme40.i
    cdleme40.n
    @20
    eqid
    @21
    eqid
    @12
    eqid
    #
    @22
    eqid
    @13
    eqid
    #
    @14
    eqid
    #
    @16
    eqid
    #
    @23
    eqid
    cdleme40n
    @7
    @3
    @18
    @17
    wceq
    @3
    @4
    @1
    @2
    @0
    @6
    simp23l
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
    @12
    cU
    cE
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    @14
    @16
    cW
    @13
    @15
    vs
    cdleme40.b
    cdleme40.l
    cdleme40.j
    cdleme40.m
    cdleme40.a
    cdleme40.h
    cdleme40.u
    cdleme40.e
    cdleme40.g
    cdleme40.i
    cdleme40.n
    cdleme40.d
    @15
    eqid
    @24
    @25
    @26
    @27
    cdleme40v
    syl
    neeqtrrd
end
