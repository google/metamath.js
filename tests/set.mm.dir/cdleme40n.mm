include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "csb.mm"
include "cvv.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cv.mm"
include "nfv.mm"
include "wnf.mm"
include "nfcv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nfne.mm"
include "a1i.mm"
include "wb.mm"
include "neeq2.mm"
include "adantl.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpl21.mm"
include "simpl22.mm"
include "simpl23.mm"
include "simpl3.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "3jca.mm"
include "cdleme40m.mm"
include "syl332anc.mm"
include "ex.mm"
include "simp1.mm"
include "simp23l.mm"
include "simp23r.mm"
include "simp21.mm"
include "simp32.mm"
include "cdleme25cl.mm"
include "syl122anc.mm"
include "wrex.mm"
include "simp11.mm"
include "simp12.mm"
include "simp13.mm"
include "cdlemb2.mm"
include "syl121anc.mm"
include "riotasv3d.mm"
include "mpan2.mm"
include "cdleme31sn1c.mm"
include "syl2anc.mm"
include "neeqtrrd.mm"

theorem cdleme40n
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.lt: class .<
  let cT: class T
  let cU: class U
  let cE: class E
  let cF: class F
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
  let cZ: class Z
  let vs: setvar s
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
  assume cdleme40a1.y: |- Y = ( ( P .\/ Q ) ./\ ( E .\/ ( ( R .\/ t ) ./\ W ) ) )
  assume cdleme40a1.c: |- C = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = Y ) )
  assume cdleme40.t: |- T = ( ( v .\/ U ) ./\ ( Q .\/ ( ( P .\/ v ) ./\ W ) ) )
  assume cdleme40.f: |- F = ( ( P .\/ Q ) ./\ ( T .\/ ( ( S .\/ v ) ./\ W ) ) )
  assume cdleme40a1.x: |- X = ( ( P .\/ Q ) ./\ ( T .\/ ( ( u .\/ v ) ./\ W ) ) )
  assume cdleme40.o: |- O = ( iota_ z e. B A. v e. A ( ( -. v .<_ W /\ -. v .<_ ( P .\/ Q ) ) -> z = X ) )
  assume cdleme40.v: |- V = if ( u .<_ ( P .\/ Q ) , O , .< )
  assume cdleme40a1.z: |- Z = ( iota_ z e. B A. v e. A ( ( -. v .<_ W /\ -. v .<_ ( P .\/ Q ) ) -> z = F ) )

  disjoint D v
  disjoint I v
  disjoint N v
  disjoint u v
  disjoint u z
  disjoint A u
  disjoint v z
  disjoint A v
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B z
  disjoint F z
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
  disjoint S u
  disjoint S z
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
  disjoint F t
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
  disjoint t v
  disjoint S v
  disjoint S y
  disjoint v y
  disjoint T s
  disjoint T t
  disjoint T y
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ S .<_ ( P .\/ Q ) /\ R =/= S ) ) -> [_ R / s ]_ N =/= [_ S / u ]_ V )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
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
    @10
    c.le
    wbr
    #
    cR
    cS
    wne
    #
    w3a
    #
    w3a
    #
    vs
    cR
    cN
    csb
    #
    cZ
    vu
    cS
    cV
    csb
    #
    @15
    cB
    cvv
    wcel
    @16
    cZ
    wne
    #
    cB
    cK
    cbs
    cfv
    cvv
    cdleme40.b
    cK
    cbs
    fvex
    eqeltri
    @15
    vv
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @19
    @10
    c.le
    wbr
    wn
    #
    wa
    #
    @16
    cF
    wne
    #
    @18
    vz
    vv
    cB
    cA
    cF
    cZ
    cvv
    @15
    vv
    nfv
    @18
    vv
    wnf
    @15
    vv
    @16
    cZ
    vv
    @16
    nfcv
    vv
    cZ
    @22
    vz
    cv
    cF
    wceq
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
    cdleme40a1.z
    @25
    vv
    vz
    cB
    @24
    vv
    cA
    nfra1
    vv
    cB
    nfcv
    nfriota
    nfcxfr
    nfne
    a1i
    cZ
    @26
    wceq
    @15
    cdleme40a1.z
    a1i
    cF
    cZ
    wceq
    @23
    @18
    wb
    @15
    cF
    cZ
    @16
    neeq2
    adantl
    @15
    @19
    cA
    wcel
    #
    @22
    wa
    #
    @23
    @15
    @28
    wa
    #
    @0
    @1
    @2
    @4
    @5
    @8
    @14
    @27
    @20
    @21
    w3a
    @23
    @0
    @1
    @2
    @9
    @14
    @28
    simpl11
    @0
    @1
    @2
    @9
    @14
    @28
    simpl12
    @0
    @1
    @2
    @9
    @14
    @28
    simpl13
    @4
    @5
    @8
    @3
    @14
    @28
    simpl21
    @4
    @5
    @8
    @3
    @14
    @28
    simpl22
    @4
    @5
    @8
    @3
    @14
    @28
    simpl23
    @3
    @9
    @14
    @28
    simpl3
    @29
    @27
    @20
    @21
    @15
    @27
    @22
    simprl
    @15
    @27
    @20
    @21
    simprrl
    @15
    @27
    @20
    @21
    simprrr
    3jca
    vy
    vv
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    cT
    cU
    cE
    cF
    cG
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cY
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
    cdleme40a1.y
    cdleme40a1.c
    cdleme40.t
    cdleme40.f
    cdleme40m
    syl332anc
    ex
    @15
    @3
    @6
    @7
    @4
    @12
    cZ
    cB
    wcel
    @3
    @9
    @14
    simp1
    @6
    @7
    @4
    @5
    @3
    @14
    simp23l
    #
    @6
    @7
    @4
    @5
    @3
    @14
    simp23r
    @3
    @4
    @5
    @8
    @14
    simp21
    #
    @3
    @9
    @11
    @12
    @13
    simp32
    #
    vz
    cA
    cB
    cP
    cQ
    cS
    cU
    cT
    cH
    cZ
    c.or
    cK
    c.le
    c.an
    cF
    cW
    vv
    cdleme40.b
    cdleme40.l
    cdleme40.j
    cdleme40.m
    cdleme40.a
    cdleme40.h
    cdleme40.u
    cdleme40.t
    cdleme40.f
    cdleme40a1.z
    cdleme25cl
    syl122anc
    @15
    @0
    @1
    @2
    @4
    @22
    vv
    cA
    wrex
    @0
    @1
    @2
    @9
    @14
    simp11
    @0
    @1
    @2
    @9
    @14
    simp12
    @0
    @1
    @2
    @9
    @14
    simp13
    @31
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    cW
    vv
    cdleme40.l
    cdleme40.j
    cdleme40.a
    cdleme40.h
    cdlemb2
    syl121anc
    riotasv3d
    mpan2
    @15
    @6
    @12
    @17
    cZ
    wceq
    @30
    @32
    vz
    vv
    cA
    cB
    cZ
    c.lt
    cP
    cQ
    cS
    cT
    cX
    cO
    c.or
    c.le
    c.an
    cV
    cW
    cF
    vu
    cdleme40a1.x
    cdleme40.o
    cdleme40.v
    cdleme40.f
    cdleme40a1.z
    cdleme31sn1c
    syl2anc
    neeqtrrd
end
