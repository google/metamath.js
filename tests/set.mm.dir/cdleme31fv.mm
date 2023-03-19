include "wcel.mm"
include "wne.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cif.mm"
include "cvv.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wi.mm"
include "wral.mm"
include "crio.mm"
include "riotaex.mm"
include "eqeltri.mm"
include "ifexg.mm"
include "mpan.mm"
include "breq1.mm"
include "notbid.mm"
include "anbi2d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "id.mm"
include "eqeq12d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "riotabidv.mm"
include "3eqtr4g.mm"
include "ifbieq12d.mm"
include "fvmptg.mm"
include "mpdan.mm"

theorem cdleme31fv
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cF: class F
  let c.or: class .\/
  let c.le: class .<_
  let c.an: class ./\
  let cN: class N
  let cO: class O
  let cW: class W
  let cX: class X
  let vs: setvar s
  assume cdleme31.o: |- O = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( x ./\ W ) ) = x ) -> z = ( N .\/ ( x ./\ W ) ) ) )
  assume cdleme31.f: |- F = ( x e. B |-> if ( ( P =/= Q /\ -. x .<_ W ) , O , x ) )
  assume cdleme31.c: |- C = ( iota_ z e. B A. s e. A ( ( -. s .<_ W /\ ( s .\/ ( X ./\ W ) ) = X ) -> z = ( N .\/ ( X ./\ W ) ) ) )

  disjoint B x
  disjoint C x
  disjoint .<_ x
  disjoint P x
  disjoint Q x
  disjoint W x
  disjoint s x
  disjoint s z
  disjoint X s
  disjoint x z
  disjoint X x
  disjoint X z
  assert |- ( X e. B -> ( F ` X ) = if ( ( P =/= Q /\ -. X .<_ W ) , C , X ) )

  proof
    cX
    cB
    wcel
    #
    cP
    cQ
    wne
    #
    cX
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cC
    cX
    cif
    #
    cvv
    wcel
    #
    cX
    cF
    cfv
    @5
    wceq
    cC
    cvv
    wcel
    @0
    @6
    cC
    vs
    cv
    #
    cW
    c.le
    wbr
    wn
    #
    @7
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
    vz
    cv
    #
    cN
    @9
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
    cvv
    cdleme31.c
    @17
    vz
    cB
    riotaex
    eqeltri
    @4
    cC
    cX
    cvv
    cB
    ifexg
    mpan
    vx
    cX
    @1
    vx
    cv
    #
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    cO
    @19
    cif
    @5
    cB
    cvv
    cF
    @19
    cX
    wceq
    #
    @22
    @4
    cO
    @19
    cC
    cX
    @23
    @21
    @3
    @1
    @23
    @20
    @2
    @19
    cX
    cW
    c.le
    breq1
    notbid
    anbi2d
    @23
    @8
    @7
    @19
    cW
    c.an
    co
    #
    c.or
    co
    #
    @19
    wceq
    #
    wa
    #
    @13
    cN
    @24
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
    @18
    cO
    cC
    @23
    @31
    @17
    vz
    cB
    @23
    @30
    @16
    vs
    cA
    @23
    @27
    @12
    @29
    @15
    @23
    @26
    @11
    @8
    @23
    @25
    @10
    @19
    cX
    @23
    @24
    @9
    @7
    c.or
    @19
    cX
    cW
    c.an
    oveq1
    #
    oveq2d
    @23
    id
    #
    eqeq12d
    anbi2d
    @23
    @28
    @14
    @13
    @23
    @24
    @9
    cN
    c.or
    @32
    oveq2d
    eqeq2d
    imbi12d
    ralbidv
    riotabidv
    cdleme31.o
    cdleme31.c
    3eqtr4g
    @33
    ifbieq12d
    cdleme31.f
    fvmptg
    mpdan
end
