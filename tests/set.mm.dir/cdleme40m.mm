include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "simp22l.mm"
include "simp3l1.mm"
include "cdleme31sn1c.mm"
include "syl2anc.mm"
include "cvv.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "nfv.mm"
include "wnf.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nfne.mm"
include "a1i.mm"
include "wb.mm"
include "neeq1.mm"
include "adantl.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3l.mm"
include "simprl.mm"
include "simprrl.mm"
include "simprrr.mm"
include "jca31.mm"
include "simp3r1.mm"
include "simp3r2.mm"
include "simp3r3.mm"
include "adantr.mm"
include "cdleme39n.mm"
include "syl113anc.mm"
include "ex.mm"
include "simp1.mm"
include "simp22r.mm"
include "simp21.mm"
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
include "eqnetrd.mm"

theorem cdleme40m
  let vy: setvar y
  let vv: setvar v
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
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
  let cW: class W
  let cY: class Y
  let vs: setvar s
  let vu: setvar u
  let vz: setvar z
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

  disjoint A v
  disjoint B v
  disjoint H v
  disjoint .\/ v
  disjoint K v
  disjoint .<_ v
  disjoint ./\ v
  disjoint P v
  disjoint Q v
  disjoint R v
  disjoint U v
  disjoint W v
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
  disjoint u v
  disjoint u z
  disjoint A u
  disjoint v z
  disjoint A z
  disjoint B u
  disjoint B z
  disjoint F z
  disjoint H z
  disjoint .\/ u
  disjoint .\/ z
  disjoint K z
  disjoint .<_ u
  disjoint .<_ z
  disjoint ./\ u
  disjoint ./\ z
  disjoint P u
  disjoint P z
  disjoint Q u
  disjoint Q z
  disjoint R z
  disjoint S u
  disjoint S z
  disjoint T u
  disjoint U z
  disjoint W u
  disjoint W z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( ( R .<_ ( P .\/ Q ) /\ S .<_ ( P .\/ Q ) /\ R =/= S ) /\ ( v e. A /\ -. v .<_ W /\ -. v .<_ ( P .\/ Q ) ) ) ) -> [_ R / s ]_ N =/= F )

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
    vv
    cv
    #
    cA
    wcel
    #
    @15
    cW
    c.le
    wbr
    wn
    #
    @15
    @10
    c.le
    wbr
    wn
    #
    w3a
    #
    wa
    #
    w3a
    #
    vs
    cR
    cN
    csb
    #
    cC
    cF
    @21
    @5
    @11
    @22
    cC
    wceq
    @5
    @6
    @4
    @8
    @3
    @20
    simp22l
    #
    @11
    @12
    @13
    @19
    @3
    @9
    simp3l1
    #
    vy
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cE
    cG
    cI
    c.or
    c.le
    c.an
    cN
    cW
    cY
    vs
    cdleme40.g
    cdleme40.i
    cdleme40.n
    cdleme40a1.y
    cdleme40a1.c
    cdleme31sn1c
    syl2anc
    @21
    cB
    cvv
    wcel
    cC
    cF
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
    @21
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @26
    @10
    c.le
    wbr
    wn
    #
    wa
    #
    cY
    cF
    wne
    #
    @25
    vy
    vt
    cB
    cA
    cY
    cC
    cvv
    @21
    vt
    nfv
    @25
    vt
    wnf
    @21
    vt
    cC
    cF
    vt
    cC
    @29
    vy
    cv
    cY
    wceq
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
    cdleme40a1.c
    @32
    vt
    vy
    cB
    @31
    vt
    cA
    nfra1
    vt
    cB
    nfcv
    nfriota
    nfcxfr
    vt
    cF
    nfcv
    nfne
    a1i
    cC
    @33
    wceq
    @21
    cdleme40a1.c
    a1i
    cY
    cC
    wceq
    @30
    @25
    wb
    @21
    cY
    cC
    cF
    neeq1
    adantl
    @21
    @26
    cA
    wcel
    #
    @29
    wa
    #
    @30
    @21
    @35
    wa
    #
    @3
    @9
    @14
    @34
    @27
    wa
    @28
    wa
    @16
    @17
    wa
    @18
    wa
    #
    @30
    @3
    @9
    @20
    @35
    simpl1
    @3
    @9
    @20
    @35
    simpl2
    @14
    @19
    @3
    @9
    @35
    simpl3l
    @36
    @34
    @27
    @28
    @21
    @34
    @29
    simprl
    @21
    @34
    @27
    @28
    simprrl
    @21
    @34
    @27
    @28
    simprrr
    jca31
    @21
    @37
    @35
    @21
    @16
    @17
    @18
    @16
    @17
    @18
    @14
    @3
    @9
    simp3r1
    @16
    @17
    @18
    @14
    @3
    @9
    simp3r2
    @16
    @17
    @18
    @14
    @3
    @9
    simp3r3
    jca31
    adantr
    vv
    vt
    cA
    cP
    cQ
    cR
    cS
    cU
    cE
    cY
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cT
    cF
    cdleme40.l
    cdleme40.j
    cdleme40.m
    cdleme40.a
    cdleme40.h
    cdleme40.u
    cdleme40.e
    cdleme40a1.y
    cdleme40.t
    cdleme40.f
    cdleme39n
    syl113anc
    ex
    @21
    @3
    @5
    @6
    @4
    @11
    cC
    cB
    wcel
    @3
    @9
    @20
    simp1
    @23
    @5
    @6
    @4
    @8
    @3
    @20
    simp22r
    @3
    @4
    @7
    @8
    @20
    simp21
    #
    @24
    vy
    cA
    cB
    cP
    cQ
    cR
    cU
    cE
    cH
    cC
    c.or
    cK
    c.le
    c.an
    cY
    cW
    vt
    cdleme40.b
    cdleme40.l
    cdleme40.j
    cdleme40.m
    cdleme40.a
    cdleme40.h
    cdleme40.u
    cdleme40.e
    cdleme40a1.y
    cdleme40a1.c
    cdleme25cl
    syl122anc
    @21
    @0
    @1
    @2
    @4
    @29
    vt
    cA
    wrex
    @0
    @1
    @2
    @9
    @20
    simp11
    @0
    @1
    @2
    @9
    @20
    simp12
    @0
    @1
    @2
    @9
    @20
    simp13
    @38
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    cW
    vt
    cdleme40.l
    cdleme40.j
    cdleme40.a
    cdleme40.h
    cdlemb2
    syl121anc
    riotasv3d
    mpan2
    eqnetrd
end
