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
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nfel1.mm"
include "nfbr.mm"
include "nfn.mm"
include "nfan.mm"
include "a1i.mm"
include "wb.mm"
include "eleq1.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi12d.mm"
include "adantl.mm"
include "simpl1.mm"
include "simpl2r.mm"
include "simprl.mm"
include "simprrl.mm"
include "jca.mm"
include "simpl2l.mm"
include "simpl3.mm"
include "simprrr.mm"
include "cdleme7ga.mm"
include "cdleme7.mm"
include "syl123anc.mm"
include "ex.mm"
include "simp1.mm"
include "simp2rl.mm"
include "simp2rr.mm"
include "simp2l.mm"
include "simp3.mm"
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
include "eleq1d.mm"
include "breq1d.mm"
include "mpbird.mm"

theorem cdlemefs32sn1aw
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
  assume cdlemefs32a1.y: |- Y = ( ( P .\/ Q ) ./\ ( D .\/ ( ( R .\/ t ) ./\ W ) ) )
  assume cdlemefs32a1.z: |- Z = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = Y ) )

  disjoint D s
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
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( P =/= Q /\ ( R e. A /\ -. R .<_ W ) ) /\ R .<_ ( P .\/ Q ) ) -> ( [_ R / s ]_ N e. A /\ -. [_ R / s ]_ N .<_ W ) )

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
    cA
    wcel
    #
    @12
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    cZ
    cA
    wcel
    #
    cZ
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @11
    cB
    cvv
    wcel
    @19
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
    @11
    vt
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @20
    @9
    c.le
    wbr
    wn
    #
    wa
    #
    cY
    cA
    wcel
    #
    cY
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @19
    vy
    vt
    cB
    cA
    cY
    cZ
    cvv
    @11
    vt
    nfv
    @19
    vt
    wnf
    @11
    @16
    @18
    vt
    vt
    cZ
    cA
    vt
    cZ
    @23
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
    cdlemefs32a1.z
    @29
    vt
    vy
    cB
    @28
    vt
    cA
    nfra1
    vt
    cB
    nfcv
    nfriota
    nfcxfr
    #
    nfel1
    @17
    vt
    vt
    cZ
    cW
    c.le
    @31
    vt
    c.le
    nfcv
    vt
    cW
    nfcv
    nfbr
    nfn
    nfan
    a1i
    cZ
    @30
    wceq
    @11
    cdlemefs32a1.z
    a1i
    cY
    cZ
    wceq
    #
    @27
    @19
    wb
    @11
    @32
    @24
    @16
    @26
    @18
    cY
    cZ
    cA
    eleq1
    @32
    @25
    @17
    cY
    cZ
    cW
    c.le
    breq1
    notbid
    anbi12d
    adantl
    @11
    @20
    cA
    wcel
    #
    @23
    wa
    #
    @27
    @11
    @34
    wa
    #
    @3
    @7
    @33
    @21
    wa
    #
    @4
    @10
    @22
    @27
    @3
    @8
    @10
    @34
    simpl1
    @4
    @7
    @3
    @10
    @34
    simpl2r
    @35
    @33
    @21
    @11
    @33
    @23
    simprl
    @11
    @33
    @21
    @22
    simprrl
    jca
    @4
    @7
    @3
    @10
    @34
    simpl2l
    @3
    @8
    @10
    @34
    simpl3
    @11
    @33
    @21
    @22
    simprrr
    @3
    @7
    @36
    wa
    @4
    @10
    @22
    w3a
    w3a
    @24
    @26
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
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.m
    cdlemefs32.a
    cdlemefs32.h
    cdlemefs32.u
    cdlemefs32.d
    cdlemefs32a1.y
    cdleme7ga
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
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.m
    cdlemefs32.a
    cdlemefs32.h
    cdlemefs32.u
    cdlemefs32.d
    cdlemefs32a1.y
    cdleme7
    jca
    syl123anc
    ex
    @11
    @3
    @5
    @6
    @4
    @10
    cZ
    cB
    wcel
    @3
    @8
    @10
    simp1
    @5
    @6
    @4
    @3
    @10
    simp2rl
    #
    @5
    @6
    @4
    @3
    @10
    simp2rr
    @3
    @4
    @7
    @10
    simp2l
    #
    @3
    @8
    @10
    simp3
    #
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
    cdlemefs32.b
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.m
    cdlemefs32.a
    cdlemefs32.h
    cdlemefs32.u
    cdlemefs32.d
    cdlemefs32a1.y
    cdlemefs32a1.z
    cdleme25cl
    syl122anc
    @11
    @0
    @1
    @2
    @4
    @23
    vt
    cA
    wrex
    @0
    @1
    @2
    @8
    @10
    simp11
    @0
    @1
    @2
    @8
    @10
    simp12
    @0
    @1
    @2
    @8
    @10
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
    cdlemefs32.l
    cdlemefs32.j
    cdlemefs32.a
    cdlemefs32.h
    cdlemb2
    syl121anc
    riotasv3d
    mpan2
    @11
    @13
    @16
    @15
    @18
    @11
    @12
    cZ
    cA
    @11
    @5
    @10
    @12
    cZ
    wceq
    @37
    @39
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
    cdlemefs32.e
    cdlemefs32.i
    cdlemefs32.n
    cdlemefs32a1.y
    cdlemefs32a1.z
    cdleme31sn1c
    syl2anc
    #
    eleq1d
    @11
    @14
    @17
    @11
    @12
    cZ
    cW
    c.le
    @40
    breq1d
    notbid
    anbi12d
    mpbird
end
