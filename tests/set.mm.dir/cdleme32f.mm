include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "cfv.mm"
include "simp11.mm"
include "simp21r.mm"
include "simp23r.mm"
include "lhpmcvr2.mm"
include "syl12anc.mm"
include "nfv.mm"
include "cif.mm"
include "cmpt.mm"
include "nfcv.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "nfra1.mm"
include "nfriota.mm"
include "nfcxfr.mm"
include "nfif.mm"
include "nfmpt.mm"
include "nffv.mm"
include "nfbr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simprl.mm"
include "simprrl.mm"
include "jca.mm"
include "simprrr.mm"
include "simpl3.mm"
include "cdleme32e.mm"
include "syl113anc.mm"
include "exp32.mm"
include "rexlimd.mm"
include "mpd.mm"

theorem cdleme32f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cE: class E
  let cF: class F
  let cH: class H
  let cI: class I
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let cY: class Y
  let vs: setvar s
  let cR: class R
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
  assume cdleme32.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme32.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )

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
  disjoint C y
  disjoint D s
  disjoint D y
  disjoint D z
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ x
  disjoint .\/ y
  disjoint .\/ z
  disjoint K s
  disjoint K t
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
  disjoint N x
  disjoint N z
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
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint H y
  disjoint K y
  disjoint Y y
  disjoint H z
  disjoint K z
  disjoint Y s
  disjoint Y t
  disjoint Y x
  disjoint Y z
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint R x
  disjoint R z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( ( X e. B /\ Y e. B ) /\ -. ( P =/= Q /\ -. X .<_ W ) /\ ( P =/= Q /\ -. Y .<_ W ) ) /\ X .<_ Y ) -> ( F ` X ) .<_ ( F ` Y ) )

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
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    wa
    #
    cP
    cQ
    wne
    #
    cX
    cW
    c.le
    wbr
    wn
    wa
    wn
    #
    @7
    cY
    cW
    c.le
    wbr
    wn
    #
    wa
    #
    w3a
    #
    cX
    cY
    c.le
    wbr
    #
    w3a
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @14
    cY
    cW
    c.an
    co
    c.or
    co
    cY
    wceq
    #
    wa
    #
    vs
    cA
    wrex
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    c.le
    wbr
    #
    @13
    @0
    @5
    @9
    @18
    @0
    @1
    @2
    @11
    @12
    simp11
    @4
    @5
    @8
    @10
    @3
    @12
    simp21r
    @7
    @9
    @6
    @8
    @3
    @12
    simp23r
    cA
    cB
    cH
    c.or
    cK
    c.le
    c.an
    cW
    cY
    vs
    cdleme32.b
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    lhpmcvr2
    syl12anc
    @13
    @17
    @21
    vs
    cA
    @13
    vs
    nfv
    vs
    @19
    @20
    c.le
    vs
    cX
    cF
    vs
    cF
    vx
    cB
    @7
    vx
    cv
    #
    cW
    c.le
    wbr
    wn
    wa
    #
    cO
    @22
    cif
    #
    cmpt
    cdleme32.f
    vs
    vx
    cB
    @24
    vs
    cB
    nfcv
    #
    @23
    vs
    cO
    @22
    @23
    vs
    nfv
    vs
    cO
    @15
    @14
    @22
    cW
    c.an
    co
    #
    c.or
    co
    @22
    wceq
    wa
    vz
    cv
    cN
    @26
    c.or
    co
    wceq
    wi
    #
    vs
    cA
    wral
    #
    vz
    cB
    crio
    cdleme32.o
    @28
    vs
    vz
    cB
    @27
    vs
    cA
    nfra1
    @25
    nfriota
    nfcxfr
    vs
    @22
    nfcv
    nfif
    nfmpt
    nfcxfr
    #
    vs
    cX
    nfcv
    nffv
    vs
    c.le
    nfcv
    vs
    cY
    cF
    @29
    vs
    cY
    nfcv
    nffv
    nfbr
    @13
    @14
    cA
    wcel
    #
    @17
    @21
    @13
    @30
    @17
    wa
    #
    wa
    #
    @3
    @11
    @30
    @15
    wa
    @16
    @12
    @21
    @3
    @11
    @12
    @31
    simpl1
    @3
    @11
    @12
    @31
    simpl2
    @32
    @30
    @15
    @13
    @30
    @17
    simprl
    @13
    @30
    @15
    @16
    simprrl
    jca
    @13
    @30
    @15
    @16
    simprrr
    @3
    @11
    @12
    @31
    simpl3
    vx
    vy
    vz
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cU
    cE
    cF
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cO
    cW
    cX
    cY
    vs
    cdleme32.b
    cdleme32.l
    cdleme32.j
    cdleme32.m
    cdleme32.a
    cdleme32.h
    cdleme32.u
    cdleme32.c
    cdleme32.d
    cdleme32.e
    cdleme32.i
    cdleme32.n
    cdleme32.o
    cdleme32.f
    cdleme32e
    syl113anc
    exp32
    rexlimd
    mpd
end
