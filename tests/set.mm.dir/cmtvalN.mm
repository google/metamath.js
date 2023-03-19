include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "copab.mm"
include "wb.mm"
include "cmtfvalN.mm"
include "df-3an.mm"
include "opabbii.mm"
include "syl6eq.mm"
include "breqd.mm"
include "3ad2ant1.mm"
include "cop.mm"
include "df-br.mm"
include "id.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "opelopab2.mm"
include "syl5bb.mm"
include "3adant1.mm"
include "bitrd.mm"

theorem cmtvalN
  let cA: class A
  let cB: class B
  let cC: class C
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  assume cmtfval.b: |- B = ( Base ` K )
  assume cmtfval.j: |- .\/ = ( join ` K )
  assume cmtfval.m: |- ./\ = ( meet ` K )
  assume cmtfval.o: |- ._|_ = ( oc ` K )
  assume cmtfval.c: |- C = ( cm ` K )


  assert |- ( ( K e. A /\ X e. B /\ Y e. B ) -> ( X C Y <-> X = ( ( X ./\ Y ) .\/ ( X ./\ ( ._|_ ` Y ) ) ) ) )

  proof
    cK
    cA
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    cX
    cY
    cC
    wbr
    #
    cX
    cY
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
    wa
    @4
    @4
    @6
    c.an
    co
    #
    @4
    @6
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
    wa
    #
    vx
    vy
    copab
    #
    wbr
    #
    cX
    cX
    cY
    c.an
    co
    #
    cX
    cY
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
    @0
    @1
    @3
    @15
    wb
    @2
    @0
    cC
    @14
    cX
    cY
    @0
    cC
    @5
    @7
    @12
    w3a
    #
    vx
    vy
    copab
    @14
    vx
    vy
    cA
    cB
    cC
    c.or
    cK
    c.an
    c.pe
    cmtfval.b
    cmtfval.j
    cmtfval.m
    cmtfval.o
    cmtfval.c
    cmtfvalN
    @21
    @13
    vx
    vy
    @5
    @7
    @12
    df-3an
    opabbii
    syl6eq
    breqd
    3ad2ant1
    @1
    @2
    @15
    @20
    wb
    @0
    @15
    cX
    cY
    cop
    @14
    wcel
    @1
    @2
    wa
    @20
    cX
    cY
    @14
    df-br
    @12
    cX
    cX
    @6
    c.an
    co
    #
    cX
    @9
    c.an
    co
    #
    c.or
    co
    #
    wceq
    @20
    vx
    vy
    cX
    cY
    cB
    cB
    @4
    cX
    wceq
    #
    @4
    cX
    @11
    @24
    @25
    id
    @25
    @8
    @22
    @10
    @23
    c.or
    @4
    cX
    @6
    c.an
    oveq1
    @4
    cX
    @9
    c.an
    oveq1
    oveq12d
    eqeq12d
    @6
    cY
    wceq
    #
    @24
    @19
    cX
    @26
    @22
    @16
    @23
    @18
    c.or
    @6
    cY
    cX
    c.an
    oveq2
    @26
    @9
    @17
    cX
    c.an
    @6
    cY
    c.pe
    fveq2
    oveq2d
    oveq12d
    eqeq2d
    opelopab2
    syl5bb
    3adant1
    bitrd
end
