include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "wne.mm"
include "csb.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "simp2l.mm"
include "atbase.mm"
include "syl.mm"
include "eqid.mm"
include "cdleme31so.mm"
include "simp1.mm"
include "simp3.mm"
include "simp2.mm"
include "cdleme32snb.mm"
include "syl12anc.mm"
include "wb.mm"
include "wnf.mm"
include "wal.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfeq2.mm"
include "nfim.mm"
include "breq1.mm"
include "notbid.mm"
include "csbeq1a.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ax-gen.mm"
include "ceqsralt.mm"
include "mp3an12.mm"
include "adantr.mm"
include "3ad2ant2.mm"
include "cp0.mm"
include "cfv.mm"
include "simp11.mm"
include "lhpmat.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "col.mm"
include "simp11l.mm"
include "hlol.mm"
include "ad2antrl.mm"
include "olj01.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simpl13.mm"
include "simpr.mm"
include "simpl3.mm"
include "cdleme27cl.mm"
include "syl122anc.mm"
include "expr.mm"
include "pm5.74d.mm"
include "impexp.mm"
include "bi2.04.mm"
include "3bitr4g.mm"
include "ralbidva.mm"
include "simp2r.mm"
include "biimt.mm"
include "3bitr4d.mm"
include "riota5.mm"

theorem cdleme32fva
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
  let cR: class R
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
  let vs: setvar s
  let cX: class X
  let cY: class Y
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
  disjoint R s
  disjoint R t
  disjoint R y
  disjoint H y
  disjoint K y
  disjoint R x
  disjoint R z
  disjoint H z
  disjoint K z
  disjoint X s
  disjoint X t
  disjoint X x
  disjoint X z
  disjoint Y y
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ ( R e. A /\ -. R .<_ W ) /\ P =/= Q ) -> [_ R / x ]_ O = [_ R / s ]_ N )

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
    cP
    cQ
    wne
    #
    w3a
    #
    vx
    cR
    cO
    csb
    #
    vs
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @13
    cR
    cW
    c.an
    co
    #
    c.or
    co
    #
    cR
    wceq
    #
    wa
    vz
    cv
    #
    cN
    @16
    c.or
    co
    #
    wceq
    #
    wi
    #
    vs
    cA
    wral
    #
    vz
    cB
    crio
    #
    vs
    cR
    cN
    csb
    #
    @11
    cR
    cB
    wcel
    #
    @12
    @24
    wceq
    @11
    @6
    @26
    @5
    @6
    @8
    @10
    simp2l
    cA
    cB
    cR
    cK
    cdleme32.b
    cdleme32.a
    atbase
    syl
    vx
    vz
    cA
    cB
    @24
    c.or
    c.le
    c.an
    cN
    cO
    cW
    cR
    vs
    cdleme32.o
    @24
    eqid
    cdleme31so
    syl
    @11
    @23
    vz
    cB
    @25
    @11
    @5
    @10
    @9
    @25
    cB
    wcel
    @5
    @9
    @10
    simp1
    @5
    @9
    @10
    simp3
    @5
    @9
    @10
    simp2
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
    cU
    cE
    cH
    cI
    c.or
    cK
    c.le
    c.an
    cN
    cW
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
    cdleme32snb
    syl12anc
    @11
    @23
    @19
    @25
    wceq
    #
    wb
    @19
    cB
    wcel
    @11
    @13
    cR
    wceq
    #
    @15
    @19
    cN
    wceq
    #
    wi
    #
    wi
    #
    vs
    cA
    wral
    #
    @8
    @28
    wi
    #
    @23
    @28
    @9
    @5
    @33
    @34
    wb
    #
    @10
    @6
    @35
    @8
    @34
    vs
    wnf
    @29
    @31
    @34
    wb
    wi
    #
    vs
    wal
    @6
    @35
    @8
    @28
    vs
    @8
    vs
    nfv
    vs
    @19
    @25
    vs
    cR
    cN
    nfcsb1v
    nfeq2
    nfim
    @36
    vs
    @29
    @15
    @8
    @30
    @28
    @29
    @14
    @7
    @13
    cR
    cW
    c.le
    breq1
    notbid
    @29
    cN
    @25
    @19
    vs
    cR
    cN
    csbeq1a
    eqeq2d
    imbi12d
    ax-gen
    @31
    @34
    vs
    cR
    cA
    ceqsralt
    mp3an12
    adantr
    3ad2ant2
    @11
    @22
    @32
    vs
    cA
    @11
    @13
    cA
    wcel
    #
    wa
    #
    @15
    @18
    @21
    wi
    #
    wi
    @15
    @29
    @30
    wi
    #
    wi
    @22
    @32
    @38
    @15
    @39
    @40
    @11
    @37
    @15
    @39
    @40
    wb
    @11
    @37
    @15
    wa
    #
    wa
    #
    @18
    @29
    @21
    @30
    @42
    @17
    @13
    cR
    @42
    @17
    @13
    cK
    cp0
    cfv
    #
    c.or
    co
    #
    @13
    @42
    @16
    @43
    @13
    c.or
    @11
    @16
    @43
    wceq
    #
    @41
    @11
    @2
    @9
    @45
    @2
    @3
    @4
    @9
    @10
    simp11
    @27
    cA
    cR
    cH
    cK
    c.le
    c.an
    cW
    @43
    cdleme32.l
    cdleme32.m
    @43
    eqid
    #
    cdleme32.a
    cdleme32.h
    lhpmat
    syl2anc
    adantr
    #
    oveq2d
    @42
    cK
    col
    wcel
    #
    @13
    cB
    wcel
    #
    @44
    @13
    wceq
    @42
    @0
    @48
    @11
    @0
    @41
    @0
    @1
    @3
    @4
    @9
    @10
    simp11l
    adantr
    cK
    hlol
    syl
    #
    @37
    @49
    @11
    @15
    cA
    cB
    @13
    cK
    cdleme32.b
    cdleme32.a
    atbase
    ad2antrl
    cB
    c.or
    cK
    @13
    @43
    cdleme32.b
    cdleme32.j
    @46
    olj01
    syl2anc
    eqtrd
    eqeq1d
    @42
    @20
    cN
    @19
    @42
    @20
    cN
    @43
    c.or
    co
    #
    cN
    @42
    @16
    @43
    cN
    c.or
    @47
    oveq2d
    @42
    @48
    cN
    cB
    wcel
    #
    @51
    cN
    wceq
    @50
    @42
    @2
    @3
    @4
    @41
    @10
    @52
    @2
    @3
    @4
    @9
    @10
    @41
    simpl11
    @2
    @3
    @4
    @9
    @10
    @41
    simpl12
    @2
    @3
    @4
    @9
    @10
    @41
    simpl13
    @11
    @41
    simpr
    @5
    @9
    @10
    @41
    simpl3
    vt
    vy
    cA
    cB
    cN
    cI
    cP
    cQ
    cU
    cC
    cH
    c.or
    cK
    c.le
    c.an
    cE
    cW
    cD
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
    cdleme27cl
    syl122anc
    cB
    c.or
    cK
    cN
    @43
    cdleme32.b
    cdleme32.j
    @46
    olj01
    syl2anc
    eqtrd
    eqeq2d
    imbi12d
    expr
    pm5.74d
    @15
    @18
    @21
    impexp
    @29
    @15
    @30
    bi2.04
    3bitr4g
    ralbidva
    @11
    @8
    @28
    @34
    wb
    @5
    @6
    @8
    @10
    simp2r
    @8
    @28
    biimt
    syl
    3bitr4d
    adantr
    riota5
    eqtrd
end
