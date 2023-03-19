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
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "cif.mm"
include "cdleme29ex.mm"
include "eqid.mm"
include "cdleme28.mm"
include "breq1.mm"
include "notbid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "oveq1i.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "syl5eq.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "ifbieq12d.mm"
include "reusv3.mm"
include "biimpd.mm"
include "sylc.mm"

theorem cdleme29b
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cU: class U
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cW: class W
  let cX: class X
  let cZ: class Z
  let vs: setvar s
  let vt: setvar t
  let cG: class G
  let cO: class O
  let cV: class V
  assume cdleme26.b: |- B = ( Base ` K )
  assume cdleme26.l: |- .<_ = ( le ` K )
  assume cdleme26.j: |- .\/ = ( join ` K )
  assume cdleme26.m: |- ./\ = ( meet ` K )
  assume cdleme26.a: |- A = ( Atoms ` K )
  assume cdleme26.h: |- H = ( LHyp ` K )
  assume cdleme27.u: |- U = ( ( P .\/ Q ) ./\ W )
  assume cdleme27.f: |- F = ( ( s .\/ U ) ./\ ( Q .\/ ( ( P .\/ s ) ./\ W ) ) )
  assume cdleme27.z: |- Z = ( ( z .\/ U ) ./\ ( Q .\/ ( ( P .\/ z ) ./\ W ) ) )
  assume cdleme27.n: |- N = ( ( P .\/ Q ) ./\ ( Z .\/ ( ( s .\/ z ) ./\ W ) ) )
  assume cdleme27.d: |- D = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = N ) )
  assume cdleme27.c: |- C = if ( s .<_ ( P .\/ Q ) , D , F )

  disjoint s u
  disjoint s z
  disjoint A s
  disjoint u z
  disjoint A u
  disjoint A z
  disjoint B s
  disjoint B u
  disjoint B z
  disjoint F u
  disjoint H s
  disjoint H z
  disjoint .\/ s
  disjoint .\/ u
  disjoint .\/ z
  disjoint K s
  disjoint K z
  disjoint .<_ s
  disjoint .<_ u
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ u
  disjoint ./\ z
  disjoint N u
  disjoint P s
  disjoint P u
  disjoint P z
  disjoint Q s
  disjoint Q u
  disjoint Q z
  disjoint U s
  disjoint U u
  disjoint U z
  disjoint W s
  disjoint W u
  disjoint W z
  disjoint X s
  disjoint A v
  disjoint B v
  disjoint .\/ v
  disjoint .<_ v
  disjoint ./\ v
  disjoint P v
  disjoint Q v
  disjoint U v
  disjoint W v
  disjoint C v
  disjoint s v
  disjoint Z s
  disjoint u v
  disjoint Z u
  disjoint Z v
  disjoint v z
  disjoint X v
  disjoint X z
  disjoint s t
  disjoint t u
  disjoint t z
  disjoint A t
  disjoint B t
  disjoint G u
  disjoint H t
  disjoint .\/ t
  disjoint K t
  disjoint .<_ t
  disjoint ./\ t
  disjoint N t
  disjoint O s
  disjoint O u
  disjoint P t
  disjoint Q t
  disjoint U t
  disjoint V z
  disjoint W t
  disjoint t v
  disjoint C t
  disjoint X t
  assert |- ( ( ( ( K e. HL /\ W e. H ) /\ ( P e. A /\ -. P .<_ W ) /\ ( Q e. A /\ -. Q .<_ W ) ) /\ P =/= Q /\ ( X e. B /\ -. X .<_ W ) ) -> E. v e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( X ./\ W ) ) = X ) -> v = ( C .\/ ( X ./\ W ) ) ) )

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
    cP
    cQ
    wne
    cX
    cB
    wcel
    cX
    cW
    c.le
    wbr
    wn
    wa
    w3a
    vs
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @0
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
    cC
    @3
    c.or
    co
    #
    cB
    wcel
    wa
    vs
    cA
    wrex
    #
    @6
    vt
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    @9
    @3
    c.or
    co
    #
    cX
    wceq
    #
    wa
    #
    wa
    @7
    @9
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    @17
    @15
    c.le
    wbr
    wn
    wa
    #
    vu
    cv
    #
    @15
    cZ
    @9
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
    #
    wceq
    #
    wi
    #
    vz
    cA
    wral
    #
    vu
    cB
    crio
    #
    @9
    cU
    c.or
    co
    #
    cQ
    cP
    @9
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
    cif
    #
    @3
    c.or
    co
    #
    wceq
    wi
    vt
    cA
    wral
    vs
    cA
    wral
    #
    @6
    vv
    cv
    @7
    wceq
    wi
    vs
    cA
    wral
    vv
    cB
    wrex
    #
    vz
    vu
    cA
    cB
    cC
    cD
    cP
    cQ
    cU
    cF
    cH
    c.or
    cK
    c.le
    c.an
    cN
    cW
    cX
    cZ
    vs
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.f
    cdleme27.z
    cdleme27.n
    cdleme27.d
    cdleme27.c
    cdleme29ex
    vz
    vu
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cU
    @27
    cF
    @32
    cH
    c.or
    cK
    c.le
    c.an
    cN
    @23
    cW
    cX
    @33
    cZ
    vs
    cdleme26.b
    cdleme26.l
    cdleme26.j
    cdleme26.m
    cdleme26.a
    cdleme26.h
    cdleme27.u
    cdleme27.f
    cdleme27.z
    cdleme27.n
    cdleme27.d
    cdleme27.c
    @32
    eqid
    @23
    eqid
    @27
    eqid
    @33
    eqid
    cdleme28
    @8
    @35
    @36
    @6
    @14
    vv
    vs
    vt
    cB
    cA
    @7
    @34
    @0
    @9
    wceq
    #
    @2
    @11
    @5
    @13
    @37
    @1
    @10
    @0
    @9
    cW
    c.le
    breq1
    notbid
    @37
    @4
    @12
    cX
    @0
    @9
    @3
    c.or
    oveq1
    eqeq1d
    anbi12d
    @37
    @7
    @0
    @15
    c.le
    wbr
    #
    cD
    cF
    cif
    #
    @3
    c.or
    co
    @34
    cC
    @39
    @3
    c.or
    cdleme27.c
    oveq1i
    @37
    @39
    @33
    @3
    c.or
    @37
    @38
    @16
    cD
    cF
    @27
    @32
    @0
    @9
    @15
    c.le
    breq1
    @37
    cD
    @18
    @19
    cN
    wceq
    #
    wi
    #
    vz
    cA
    wral
    #
    vu
    cB
    crio
    @27
    cdleme27.d
    @37
    @42
    @26
    vu
    cB
    @37
    @41
    @25
    vz
    cA
    @37
    @40
    @24
    @18
    @37
    cN
    @23
    @19
    @37
    cN
    @15
    cZ
    @0
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
    @23
    cdleme27.n
    @37
    @45
    @22
    @15
    c.an
    @37
    @44
    @21
    cZ
    c.or
    @37
    @43
    @20
    cW
    c.an
    @0
    @9
    @17
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
    syl5eq
    @37
    cF
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
    @32
    cdleme27.f
    @37
    @46
    @28
    @49
    @31
    c.an
    @0
    @9
    cU
    c.or
    oveq1
    @37
    @48
    @30
    cQ
    c.or
    @37
    @47
    @29
    cW
    c.an
    @0
    @9
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    syl5eq
    ifbieq12d
    oveq1d
    syl5eq
    reusv3
    biimpd
    sylc
end
