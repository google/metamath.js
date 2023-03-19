include "cv.mm"
include "wceq.mm"
include "co.mm"
include "wbr.mm"
include "cif.mm"
include "breq1.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "3eqtr4g.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "oveq2.mm"
include "oveq12d.mm"
include "ifbieq12d.mm"

theorem cdleme27b
  let vz: setvar z
  let vu: setvar u
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
  let cG: class G
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let vs: setvar s
  let cV: class V
  let cX: class X
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
  assume cdleme27.g: |- G = ( ( t .\/ U ) ./\ ( Q .\/ ( ( P .\/ t ) ./\ W ) ) )
  assume cdleme27.o: |- O = ( ( P .\/ Q ) ./\ ( Z .\/ ( ( t .\/ z ) ./\ W ) ) )
  assume cdleme27.e: |- E = ( iota_ u e. B A. z e. A ( ( -. z .<_ W /\ -. z .<_ ( P .\/ Q ) ) -> u = O ) )
  assume cdleme27.y: |- Y = if ( t .<_ ( P .\/ Q ) , E , G )

  disjoint s t
  disjoint s u
  disjoint s z
  disjoint A s
  disjoint t u
  disjoint t z
  disjoint A t
  disjoint u z
  disjoint A u
  disjoint A z
  disjoint B s
  disjoint B t
  disjoint B u
  disjoint B z
  disjoint F u
  disjoint G u
  disjoint H s
  disjoint H t
  disjoint H z
  disjoint .\/ s
  disjoint .\/ t
  disjoint .\/ u
  disjoint .\/ z
  disjoint K s
  disjoint K t
  disjoint K z
  disjoint .<_ s
  disjoint .<_ t
  disjoint .<_ u
  disjoint .<_ z
  disjoint ./\ s
  disjoint ./\ t
  disjoint ./\ u
  disjoint ./\ z
  disjoint N t
  disjoint N u
  disjoint O s
  disjoint O u
  disjoint P s
  disjoint P t
  disjoint P u
  disjoint P z
  disjoint Q s
  disjoint Q t
  disjoint Q u
  disjoint Q z
  disjoint U s
  disjoint U t
  disjoint U u
  disjoint U z
  disjoint W s
  disjoint W t
  disjoint W u
  disjoint W z
  disjoint V z
  disjoint X s
  assert |- ( s = t -> C = Y )

  proof
    vs
    cv
    #
    vt
    cv
    #
    wceq
    #
    @0
    cP
    cQ
    c.or
    co
    #
    c.le
    wbr
    #
    cD
    cF
    cif
    @1
    @3
    c.le
    wbr
    #
    cE
    cG
    cif
    cC
    cY
    @2
    @4
    @5
    cD
    cF
    cE
    cG
    @0
    @1
    @3
    c.le
    breq1
    @2
    vz
    cv
    #
    cW
    c.le
    wbr
    wn
    @6
    @3
    c.le
    wbr
    wn
    wa
    #
    vu
    cv
    #
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
    @7
    @8
    cO
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
    cD
    cE
    @2
    @11
    @14
    vu
    cB
    @2
    @10
    @13
    vz
    cA
    @2
    @9
    @12
    @7
    @2
    cN
    cO
    @8
    @2
    @3
    cZ
    @0
    @6
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
    @3
    cZ
    @1
    @6
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
    cN
    cO
    @2
    @17
    @20
    @3
    c.an
    @2
    @16
    @19
    cZ
    c.or
    @2
    @15
    @18
    cW
    c.an
    @0
    @1
    @6
    c.or
    oveq1
    oveq1d
    oveq2d
    oveq2d
    cdleme27.n
    cdleme27.o
    3eqtr4g
    eqeq2d
    imbi2d
    ralbidv
    riotabidv
    cdleme27.d
    cdleme27.e
    3eqtr4g
    @2
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
    @1
    cU
    c.or
    co
    #
    cQ
    cP
    @1
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
    cF
    cG
    @2
    @21
    @25
    @24
    @28
    c.an
    @0
    @1
    cU
    c.or
    oveq1
    @2
    @23
    @27
    cQ
    c.or
    @2
    @22
    @26
    cW
    c.an
    @0
    @1
    cP
    c.or
    oveq2
    oveq1d
    oveq2d
    oveq12d
    cdleme27.f
    cdleme27.g
    3eqtr4g
    ifbieq12d
    cdleme27.c
    cdleme27.y
    3eqtr4g
end
