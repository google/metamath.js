include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "csb.mm"
include "wceq.mm"
include "simp2rl.mm"
include "simp3.mm"
include "cdleme31sn1c.mm"
include "syl2anc.mm"
include "cvv.mm"
include "cbs.mm"
include "cfv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cv.mm"
include "nfv.mm"
include "wnf.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nfbr.mm"
include "a1i.mm"
include "wb.mm"
include "breq1.mm"
include "adantl.mm"
include "simpl11.mm"
include "simp12l.mm"
include "adantr.mm"
include "simp13l.mm"
include "simprl.mm"
include "cdleme4a.mm"
include "syl131anc.mm"
include "ex.mm"
include "simp1.mm"
include "simp2rr.mm"
include "simp2l.mm"
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
include "eqbrtrd.mm"

theorem cdleme41sn3a
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  let cX: class X
  assume cdleme32.b: |- B = ( Base ` K )
  assume cdleme32.l: |- .<_ = ( le ` K )
  assume cdleme32.j: |- .\/ = ( join ` K )
  assume cdleme32.m: |- ./\ = ( meet ` K )
  assume cdleme32.a: |- A = ( Atoms ` K )
  assume cdleme32.h: |- H = ( LHyp ` K )
  assume cdleme32.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme32.c: |- C = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme32.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme32.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme32.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) )
  assume cdleme32.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )
  assume cdleme32a1.y: |- Y = ( ( P .\/ Q ) ./\ ( D .\/ ( ( R .\/ t ) ./\ W ) ) )
  assume cdleme32a1.z: |- Z = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = Y ) )

  disjoint s t
  disjoint s y
  disjoint A s
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint B s
  disjoint B t
  disjoint B y
  disjoint C y
  disjoint D s
  disjoint D y
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ y
  disjoint K s
  disjoint K t
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
  disjoint U s
  disjoint U t
  disjoint U y
  disjoint W s
  disjoint W t
  disjoint W y
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint H y
  disjoint K y
  disjoint Y y
  disjoint s x
  disjoint s z
  disjoint t x
  disjoint t z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint D z
  disjoint .\/ x
  disjoint .\/ z
  disjoint .<_ x
  disjoint .<_ z
  disjoint ./\ x
  disjoint ./\ z
  disjoint N x
  disjoint N z
  disjoint P x
  disjoint P z
  disjoint Q x
  disjoint Q z
  disjoint U x
  disjoint U z
  disjoint W x
  disjoint W z
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ R .<_ ( P .\/ Q ) ) -> [_ R / s ]_ N .<_ ( P .\/ Q ) )

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
    wa
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
    w3a
    #
    vs
    cR
    cN
    csb
    #
    cZ
    @13
    c.le
    @15
    @9
    @14
    @16
    cZ
    wceq
    @9
    @10
    @8
    @7
    @14
    simp2rl
    #
    @7
    @12
    @14
    simp3
    #
    vy
    vt
    cA
    cB
    cZ
    cC
    cP
    cQ
    cR
    cD
    cE
    cI
    c.or
    c.le
    c.an
    cN
    cW
    cY
    vs
    cdleme32.e
    cdleme32.i
    cdleme32.n
    cdleme32a1.y
    cdleme32a1.z
    cdleme31sn1c
    syl2anc
    @15
    cB
    cvv
    wcel
    cZ
    @13
    c.le
    wbr
    #
    cB
    cK
    cbs
    cfv
    cvv
    cdleme32.b
    cK
    cbs
    fvex
    eqeltri
    @15
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    @20
    @13
    c.le
    wbr
    wn
    wa
    #
    cY
    @13
    c.le
    wbr
    #
    @19
    vy
    vt
    cB
    cA
    cY
    cZ
    cvv
    @15
    vt
    nfv
    @19
    vt
    wnf
    @15
    vt
    cZ
    @13
    c.le
    vt
    cZ
    @21
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
    cdleme32a1.z
    @24
    vt
    vy
    cB
    @23
    vt
    cA
    nfra1
    vt
    cB
    nfcv
    nfriota
    nfcxfr
    vt
    c.le
    nfcv
    vt
    @13
    nfcv
    nfbr
    a1i
    cZ
    @25
    wceq
    @15
    cdleme32a1.z
    a1i
    cY
    cZ
    wceq
    @22
    @19
    wb
    @15
    cY
    cZ
    @13
    c.le
    breq1
    adantl
    @15
    @20
    cA
    wcel
    #
    @21
    wa
    #
    @22
    @15
    @27
    wa
    @0
    @1
    @4
    @9
    @26
    @22
    @0
    @3
    @6
    @12
    @14
    @27
    simpl11
    @15
    @1
    @27
    @1
    @2
    @0
    @6
    @12
    @14
    simp12l
    adantr
    @15
    @4
    @27
    @4
    @5
    @0
    @3
    @12
    @14
    simp13l
    adantr
    @15
    @9
    @27
    @17
    adantr
    @15
    @26
    @21
    simprl
    cA
    cP
    cQ
    cR
    @20
    cU
    cD
    cY
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    cdleme32.u
    cdleme32.d
    cdleme32a1.y
    cdleme4a
    syl131anc
    ex
    @15
    @7
    @9
    @10
    @8
    @14
    cZ
    cB
    wcel
    @7
    @12
    @14
    simp1
    @17
    @9
    @10
    @8
    @7
    @14
    simp2rr
    @7
    @8
    @11
    @14
    simp2l
    #
    @18
    vy
    cA
    cB
    cP
    cQ
    cR
    cU
    cD
    cH
    cZ
    c.or
    cK
    c.le
    c.an
    cY
    cW
    vt
    cdleme32.b
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    cdleme32.u
    cdleme32.d
    cdleme32a1.y
    cdleme32a1.z
    cdleme25cl
    syl122anc
    @15
    @0
    @3
    @6
    @8
    @21
    vt
    cA
    wrex
    @0
    @3
    @6
    @12
    @14
    simp11
    @0
    @3
    @6
    @12
    @14
    simp12
    @0
    @3
    @6
    @12
    @14
    simp13
    @28
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    cW
    vt
    cdleme32.l
    cdleme32.j
    cdleme32.a
    cdleme32.h
    cdlemb2
    syl121anc
    riotasv3d
    mpan2
    eqbrtrd
end
