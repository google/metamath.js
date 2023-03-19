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
include "simp22l.mm"
include "simp3l.mm"
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
include "nfeq1.mm"
include "a1i.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantl.mm"
include "simpl1.mm"
include "simpl22.mm"
include "simprl.mm"
include "simprrl.mm"
include "jca.mm"
include "simpl23.mm"
include "simpl21.mm"
include "simprrr.mm"
include "simpl3r.mm"
include "simpl3l.mm"
include "3jca.mm"
include "eqid.mm"
include "cdleme21k.mm"
include "syl132anc.mm"
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
include "eqtrd.mm"

theorem cdleme43fsv1snlem
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cU: class U
  let cE: class E
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  assume cdlemefs32.b: |- B = ( Base ` K )
  assume cdlemefs32.l: |- .<_ = ( le ` K )
  assume cdlemefs32.j: |- .\/ = ( join ` K )
  assume cdlemefs32.m: |- ./\ = ( meet ` K )
  assume cdlemefs32.a: |- A = ( Atoms ` K )
  assume cdlemefs32.h: |- H = ( LHyp ` K )
  assume cdlemefs32.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdlemefs32.d: |- D = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdlemefs32.e: |- E = ( ( P .\/ Q ) ./\ ( D .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdlemefs32.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = E ) )
  assume cdlemefs32.n: |- N = if ( s .<_ ( P .\/ Q ) , I , C )
  assume cdleme43fs.y: |- Y = ( ( S .\/ U ) ./\ ( Q .\/ ( ( P .\/ S ) ./\ W ) ) )
  assume cdleme43fs.z: |- Z = ( ( P .\/ Q ) ./\ ( Y .\/ ( ( R .\/ S ) ./\ W ) ) )
  assume cdleme43fsa1.v: |- V = ( ( P .\/ Q ) ./\ ( D .\/ ( ( R .\/ t ) ./\ W ) ) )
  assume cdleme43fsa1.x: |- X = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = V ) )

  disjoint V y
  disjoint s t
  disjoint s y
  disjoint A s
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint B s
  disjoint B t
  disjoint B y
  disjoint D y
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint H y
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ y
  disjoint K s
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
  disjoint D s
  disjoint S t
  disjoint S y
  disjoint Z t
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
  disjoint .\/ x
  disjoint .\/ z
  disjoint .<_ x
  disjoint .<_ z
  disjoint ./\ x
  disjoint ./\ z
  disjoint N x
  disjoint N z
  disjoint P z
  disjoint Q z
  disjoint W x
  disjoint W z
  disjoint H z
  disjoint K z
  disjoint R z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) /\ ( S e. A /\ -. S .<_ W ) ) /\ ( R .<_ ( P .\/ Q ) /\ -. S .<_ ( P .\/ Q ) ) ) -> [_ R / s ]_ N = Z )

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
    wn
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
    cX
    cZ
    @14
    @5
    @11
    @15
    cX
    wceq
    @5
    @6
    @4
    @8
    @3
    @13
    simp22l
    #
    @3
    @9
    @11
    @12
    simp3l
    #
    vy
    vt
    cA
    cB
    cX
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
    cV
    vs
    cdlemefs32.e
    cdlemefs32.i
    cdlemefs32.n
    cdleme43fsa1.v
    cdleme43fsa1.x
    cdleme31sn1c
    syl2anc
    @14
    cB
    cvv
    wcel
    cX
    cZ
    wceq
    #
    cB
    cK
    cbs
    cfv
    cvv
    cdlemefs32.b
    cK
    cbs
    fvex
    eqeltri
    @14
    vt
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
    cV
    cZ
    wceq
    #
    @18
    vy
    vt
    cB
    cA
    cV
    cX
    cvv
    @14
    vt
    nfv
    @18
    vt
    wnf
    @14
    vt
    cX
    cZ
    vt
    cX
    @22
    vy
    cv
    cV
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
    cdleme43fsa1.x
    @25
    vt
    vy
    cB
    @24
    vt
    cA
    nfra1
    vt
    cB
    nfcv
    nfriota
    nfcxfr
    nfeq1
    a1i
    cX
    @26
    wceq
    @14
    cdleme43fsa1.x
    a1i
    cV
    cX
    wceq
    @23
    @18
    wb
    @14
    cV
    cX
    cZ
    eqeq1
    adantl
    @14
    @19
    cA
    wcel
    #
    @22
    wa
    #
    @23
    @14
    @28
    wa
    #
    @3
    @7
    @27
    @20
    wa
    @8
    @4
    @21
    @12
    @11
    w3a
    @23
    @3
    @9
    @13
    @28
    simpl1
    @4
    @7
    @8
    @3
    @13
    @28
    simpl22
    @29
    @27
    @20
    @14
    @27
    @22
    simprl
    @14
    @27
    @20
    @21
    simprrl
    jca
    @4
    @7
    @8
    @3
    @13
    @28
    simpl23
    @4
    @7
    @8
    @3
    @13
    @28
    simpl21
    @29
    @21
    @12
    @11
    @14
    @27
    @20
    @21
    simprrr
    @11
    @12
    @3
    @9
    @28
    simpl3r
    @11
    @12
    @3
    @9
    @28
    simpl3l
    3jca
    cA
    cR
    @19
    c.or
    co
    cW
    c.an
    co
    #
    cP
    cQ
    cR
    @19
    cS
    cU
    cD
    cY
    cH
    c.or
    cK
    c.le
    c.an
    cV
    cZ
    cW
    cR
    cS
    c.or
    co
    cW
    c.an
    co
    #
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.m
    cdlemefs32.a
    cdlemefs32.h
    cdlemefs32.u
    cdlemefs32.d
    cdleme43fs.y
    @30
    eqid
    @31
    eqid
    cdleme43fsa1.v
    cdleme43fs.z
    cdleme21k
    syl132anc
    ex
    @14
    @3
    @5
    @6
    @4
    @11
    cX
    cB
    wcel
    @3
    @9
    @13
    simp1
    @16
    @5
    @6
    @4
    @8
    @3
    @13
    simp22r
    @3
    @4
    @7
    @8
    @13
    simp21
    #
    @17
    vy
    cA
    cB
    cP
    cQ
    cR
    cU
    cD
    cH
    cX
    c.or
    cK
    c.le
    c.an
    cV
    cW
    vt
    cdlemefs32.b
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.m
    cdlemefs32.a
    cdlemefs32.h
    cdlemefs32.u
    cdlemefs32.d
    cdleme43fsa1.v
    cdleme43fsa1.x
    cdleme25cl
    syl122anc
    @14
    @0
    @1
    @2
    @4
    @22
    vt
    cA
    wrex
    @0
    @1
    @2
    @9
    @13
    simp11
    @0
    @1
    @2
    @9
    @13
    simp12
    @0
    @1
    @2
    @9
    @13
    simp13
    @32
    cA
    cP
    cQ
    cH
    c.or
    cK
    c.le
    cW
    vt
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.a
    cdlemefs32.h
    cdlemb2
    syl121anc
    riotasv3d
    mpan2
    eqtrd
end
