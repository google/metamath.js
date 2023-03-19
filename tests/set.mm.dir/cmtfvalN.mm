include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "copab.mm"
include "elex.mm"
include "ccmtN.mm"
include "cbs.mm"
include "cmee.mm"
include "coc.mm"
include "cjn.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "oveqd.mm"
include "eqidd.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "eqeq2d.mm"
include "3anbi123d.mm"
include "opabbidv.mm"
include "df-cmtN.mm"
include "wa.mm"
include "df-3an.mm"
include "opabbii.mm"
include "cxp.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem cmtfvalN
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.pe: class ._|_
  let vp: setvar p
  assume cmtfval.b: |- B = ( Base ` K )
  assume cmtfval.j: |- .\/ = ( join ` K )
  assume cmtfval.m: |- ./\ = ( meet ` K )
  assume cmtfval.o: |- ._|_ = ( oc ` K )
  assume cmtfval.c: |- C = ( cm ` K )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint p x
  disjoint p y
  disjoint B p
  disjoint .\/ p
  disjoint ./\ p
  disjoint ._|_ p
  disjoint K p
  assert |- ( K e. A -> C = { <. x , y >. | ( x e. B /\ y e. B /\ x = ( ( x ./\ y ) .\/ ( x ./\ ( ._|_ ` y ) ) ) ) } )

  proof
    cK
    cA
    wcel
    cK
    cvv
    wcel
    #
    cC
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    @1
    @1
    @3
    c.an
    co
    #
    @1
    @3
    c.pe
    cfv
    #
    c.an
    co
    #
    c.or
    co
    #
    wceq
    #
    w3a
    #
    vx
    vy
    copab
    #
    wceq
    cK
    cA
    elex
    @0
    cC
    cK
    ccmtN
    cfv
    @11
    cmtfval.c
    vp
    cK
    @1
    vp
    cv
    #
    cbs
    cfv
    #
    wcel
    #
    @3
    @13
    wcel
    #
    @1
    @1
    @3
    @12
    cmee
    cfv
    #
    co
    #
    @1
    @3
    @12
    coc
    cfv
    #
    cfv
    #
    @16
    co
    #
    @12
    cjn
    cfv
    #
    co
    #
    wceq
    #
    w3a
    #
    vx
    vy
    copab
    @11
    cvv
    ccmtN
    @12
    cK
    wceq
    #
    @24
    @10
    vx
    vy
    @25
    @14
    @2
    @15
    @4
    @23
    @9
    @25
    @13
    cB
    @1
    @25
    @13
    cK
    cbs
    cfv
    #
    cB
    @12
    cK
    cbs
    fveq2
    cmtfval.b
    syl6eqr
    #
    eleq2d
    @25
    @13
    cB
    @3
    @27
    eleq2d
    @25
    @22
    @8
    @1
    @25
    @17
    @5
    @20
    @7
    @21
    c.or
    @25
    @21
    cK
    cjn
    cfv
    c.or
    @12
    cK
    cjn
    fveq2
    cmtfval.j
    syl6eqr
    @25
    @16
    c.an
    @1
    @3
    @25
    @16
    cK
    cmee
    cfv
    c.an
    @12
    cK
    cmee
    fveq2
    cmtfval.m
    syl6eqr
    #
    oveqd
    @25
    @1
    @1
    @19
    @6
    @16
    c.an
    @28
    @25
    @1
    eqidd
    @25
    @3
    @18
    c.pe
    @25
    @18
    cK
    coc
    cfv
    c.pe
    @12
    cK
    coc
    fveq2
    cmtfval.o
    syl6eqr
    fveq1d
    oveq123d
    oveq123d
    eqeq2d
    3anbi123d
    opabbidv
    vx
    vy
    vp
    df-cmtN
    @11
    @2
    @4
    wa
    @9
    wa
    #
    vx
    vy
    copab
    #
    cvv
    @10
    @29
    vx
    vy
    @2
    @4
    @9
    df-3an
    opabbii
    @30
    cB
    cB
    cxp
    cB
    cB
    cB
    @26
    cvv
    cmtfval.b
    cK
    cbs
    fvex
    eqeltri
    #
    @31
    xpex
    @9
    vx
    vy
    cB
    cB
    opabssxp
    ssexi
    eqeltri
    fvmpt
    syl5eq
    syl
end
