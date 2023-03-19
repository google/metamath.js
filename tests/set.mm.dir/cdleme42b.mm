include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "co.mm"
include "wceq.mm"
include "cvv.mm"
include "cfv.mm"
include "csb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cv.mm"
include "nfv.mm"
include "wnfc.mm"
include "nfcsb1v.mm"
include "nfcv.mm"
include "nfov.mm"
include "a1i.mm"
include "nfvd.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "eqid.mm"
include "cdleme31fv1.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "breq1.mm"
include "notbid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "adantl.mm"
include "csbeq1a.mm"
include "oveq1d.mm"
include "simp1.mm"
include "simp2l.mm"
include "cdleme32fvcl.mm"
include "syl2anc.mm"
include "simp3ll.mm"
include "simp3lr.mm"
include "simp3r.mm"
include "jca.mm"
include "riotasv2d.mm"
include "mpan2.mm"

theorem cdleme42b
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
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
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vu: setvar u
  let cS: class S
  assume cdleme41.b: |- B = ( Base ` K )
  assume cdleme41.l: |- .<_ = ( le ` K )
  assume cdleme41.j: |- .\/ = ( join ` K )
  assume cdleme41.m: |- ./\ = ( meet ` K )
  assume cdleme41.a: |- A = ( Atoms ` K )
  assume cdleme41.h: |- H = ( LHyp ` K )
  assume cdleme41.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme41.d: |- D = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme41.e: |- E = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme41.g: |- G = ( ( P .\/ Q ) ./\ ( E .\/ ( ( s .\/ t ) ./\ W ) ) )
  assume cdleme41.i: |- I = ( iota_ y e. B A. t e. A ( ( -. t .<_ W /\ -. t .<_ ( P .\/ Q ) ) -> y = G ) )
  assume cdleme41.n: |- N = if ( s .<_ ( P .\/ Q ) , I , D )
  assume cdleme41.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme41.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )

  disjoint A s
  disjoint .\/ s
  disjoint .<_ s
  disjoint ./\ s
  disjoint P s
  disjoint Q s
  disjoint R s
  disjoint U s
  disjoint W s
  disjoint t y
  disjoint A t
  disjoint A y
  disjoint s t
  disjoint s y
  disjoint B s
  disjoint B t
  disjoint B y
  disjoint D y
  disjoint G y
  disjoint E s
  disjoint E y
  disjoint H s
  disjoint H t
  disjoint H y
  disjoint .\/ t
  disjoint .\/ y
  disjoint K s
  disjoint K t
  disjoint K y
  disjoint .<_ t
  disjoint .<_ y
  disjoint ./\ t
  disjoint ./\ y
  disjoint P t
  disjoint P y
  disjoint Q t
  disjoint Q y
  disjoint R t
  disjoint R y
  disjoint U t
  disjoint U y
  disjoint W t
  disjoint W y
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint B x
  disjoint B z
  disjoint E z
  disjoint s z
  disjoint H z
  disjoint .\/ x
  disjoint .\/ z
  disjoint K z
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
  disjoint R x
  disjoint R z
  disjoint U x
  disjoint U z
  disjoint W x
  disjoint W z
  disjoint s x
  disjoint t x
  disjoint t z
  disjoint x y
  disjoint y z
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint s u
  disjoint A u
  disjoint .\/ u
  disjoint .<_ u
  disjoint ./\ u
  disjoint N u
  disjoint P u
  disjoint Q u
  disjoint S s
  disjoint S u
  disjoint U u
  disjoint t u
  disjoint u y
  disjoint B u
  disjoint S t
  disjoint S y
  disjoint W u
  disjoint S x
  disjoint S z
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( X e. B /\ ( P =/= Q /\ -. X .<_ W ) ) /\ ( ( R e. A /\ -. R .<_ W ) /\ ( R .\/ ( X ./\ W ) ) = X ) ) -> ( F ` X ) = ( [_ R / s ]_ N .\/ ( X ./\ W ) ) )

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
    cX
    cB
    wcel
    #
    cP
    cQ
    wne
    cX
    cW
    c.le
    wbr
    wn
    wa
    #
    wa
    #
    cR
    cA
    wcel
    #
    cR
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cR
    cX
    cW
    c.an
    co
    #
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    w3a
    #
    cB
    cvv
    wcel
    cX
    cF
    cfv
    #
    vs
    cR
    cN
    csb
    #
    @8
    c.or
    co
    #
    wceq
    cB
    cK
    cbs
    cfv
    cvv
    cdleme41.b
    cK
    cbs
    fvex
    eqeltri
    @12
    vs
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @16
    @8
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    @6
    @10
    wa
    #
    vz
    vs
    cB
    cA
    cN
    @8
    c.or
    co
    #
    @13
    cR
    @15
    cvv
    @12
    vs
    nfv
    vs
    @15
    wnfc
    @12
    vs
    @14
    @8
    c.or
    vs
    cR
    cN
    nfcsb1v
    vs
    c.or
    nfcv
    vs
    @8
    nfcv
    nfov
    a1i
    @12
    @22
    vs
    nfvd
    @3
    @0
    @13
    @21
    vz
    cv
    @23
    wceq
    wi
    vs
    cA
    wral
    vz
    cB
    crio
    #
    wceq
    @11
    vx
    vz
    cA
    cB
    @24
    cP
    cQ
    cF
    c.or
    c.le
    c.an
    cN
    cO
    cW
    cX
    vs
    cdleme41.o
    cdleme41.f
    @24
    eqid
    cdleme31fv1
    3ad2ant2
    @16
    cR
    wceq
    #
    @21
    @22
    wb
    @12
    @25
    @18
    @6
    @20
    @10
    @25
    @17
    @5
    @16
    cR
    cW
    c.le
    breq1
    notbid
    @25
    @19
    @9
    cX
    @16
    cR
    @8
    c.or
    oveq1
    eqeq1d
    anbi12d
    adantl
    @25
    @23
    @15
    wceq
    @12
    @25
    cN
    @14
    @8
    c.or
    vs
    cR
    cN
    csbeq1a
    oveq1d
    adantl
    @12
    @0
    @1
    @13
    cB
    wcel
    @0
    @3
    @11
    simp1
    @0
    @1
    @2
    @11
    simp2l
    vx
    vy
    vz
    vt
    cA
    cB
    cD
    cE
    cP
    cQ
    cU
    cG
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
    vs
    cdleme41.b
    cdleme41.l
    cdleme41.j
    cdleme41.m
    cdleme41.a
    cdleme41.h
    cdleme41.u
    cdleme41.d
    cdleme41.e
    cdleme41.g
    cdleme41.i
    cdleme41.n
    cdleme41.o
    cdleme41.f
    cdleme32fvcl
    syl2anc
    @4
    @6
    @10
    @0
    @3
    simp3ll
    @12
    @6
    @10
    @4
    @6
    @10
    @0
    @3
    simp3lr
    @0
    @3
    @7
    @10
    simp3r
    jca
    riotasv2d
    mpan2
end
