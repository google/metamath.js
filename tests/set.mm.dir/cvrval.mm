include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wn.mm"
include "copab.mm"
include "wb.mm"
include "cvrfval.mm"
include "3anass.mm"
include "opabbii.mm"
include "syl6eq.mm"
include "breqd.mm"
include "3ad2ant1.mm"
include "cop.mm"
include "df-br.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "notbid.mm"
include "anbi12d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "opelopab2.mm"
include "syl5bb.mm"
include "3adant1.mm"
include "bitrd.mm"

theorem cvrval
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  assume cvrfval.b: |- B = ( Base ` K )
  assume cvrfval.s: |- .< = ( lt ` K )
  assume cvrfval.c: |- C = ( <o ` K )

  disjoint B z
  disjoint K z
  disjoint X z
  disjoint Y z
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint B p
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint K p
  disjoint K x
  disjoint K y
  disjoint .< p
  disjoint .< x
  disjoint .< y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( ( K e. A /\ X e. B /\ Y e. B ) -> ( X C Y <-> ( X .< Y /\ -. E. z e. B ( X .< z /\ z .< Y ) ) ) )

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
    vy
    cv
    #
    cB
    wcel
    wa
    #
    @4
    @5
    c.lt
    wbr
    #
    @4
    vz
    cv
    #
    c.lt
    wbr
    #
    @8
    @5
    c.lt
    wbr
    #
    wa
    #
    vz
    cB
    wrex
    #
    wn
    #
    wa
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
    cY
    c.lt
    wbr
    #
    cX
    @8
    c.lt
    wbr
    #
    @8
    cY
    c.lt
    wbr
    #
    wa
    #
    vz
    cB
    wrex
    #
    wn
    #
    wa
    #
    @0
    @1
    @3
    @17
    wb
    @2
    @0
    cC
    @16
    cX
    cY
    @0
    cC
    @6
    @7
    @13
    w3a
    #
    vx
    vy
    copab
    @16
    vx
    vy
    vz
    cA
    cB
    cC
    c.lt
    cK
    cvrfval.b
    cvrfval.s
    cvrfval.c
    cvrfval
    @25
    @15
    vx
    vy
    @6
    @7
    @13
    3anass
    opabbii
    syl6eq
    breqd
    3ad2ant1
    @1
    @2
    @17
    @24
    wb
    @0
    @17
    cX
    cY
    cop
    @16
    wcel
    @1
    @2
    wa
    @24
    cX
    cY
    @16
    df-br
    @14
    cX
    @5
    c.lt
    wbr
    #
    @19
    @10
    wa
    #
    vz
    cB
    wrex
    #
    wn
    #
    wa
    @24
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
    @7
    @26
    @13
    @29
    @4
    cX
    @5
    c.lt
    breq1
    @30
    @12
    @28
    @30
    @11
    @27
    vz
    cB
    @30
    @9
    @19
    @10
    @4
    cX
    @8
    c.lt
    breq1
    anbi1d
    rexbidv
    notbid
    anbi12d
    @5
    cY
    wceq
    #
    @26
    @18
    @29
    @23
    @5
    cY
    cX
    c.lt
    breq2
    @31
    @28
    @22
    @31
    @27
    @21
    vz
    cB
    @31
    @10
    @20
    @19
    @5
    cY
    @8
    c.lt
    breq2
    anbi2d
    rexbidv
    notbid
    anbi12d
    opelopab2
    syl5bb
    3adant1
    bitrd
end
