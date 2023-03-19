include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wn.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cvrval.mm"
include "wb.mm"
include "wne.mm"
include "iman.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "xchbinxr.mm"
include "pltval.mm"
include "3com23.mm"
include "3expa.mm"
include "anbi2d.mm"
include "anass.mm"
include "syl6rbbr.mm"
include "notbid.mm"
include "syl5bb.mm"
include "ralbidva.mm"
include "ralnex.mm"
include "syl6bb.mm"
include "3adant2.mm"
include "bitr4d.mm"

theorem cvrval2
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  assume cvrletr.b: |- B = ( Base ` K )
  assume cvrletr.l: |- .<_ = ( le ` K )
  assume cvrletr.s: |- .< = ( lt ` K )
  assume cvrletr.c: |- C = ( <o ` K )

  disjoint A z
  disjoint B z
  disjoint K z
  disjoint X z
  disjoint Y z
  assert |- ( ( K e. A /\ X e. B /\ Y e. B ) -> ( X C Y <-> ( X .< Y /\ A. z e. B ( ( X .< z /\ z .<_ Y ) -> z = Y ) ) ) )

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
    cX
    cY
    c.lt
    wbr
    #
    cX
    vz
    cv
    #
    c.lt
    wbr
    #
    @4
    cY
    c.lt
    wbr
    #
    wa
    #
    vz
    cB
    wrex
    wn
    #
    wa
    #
    @3
    @5
    @4
    cY
    c.le
    wbr
    #
    wa
    #
    @4
    cY
    wceq
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    vz
    cA
    cB
    cC
    c.lt
    cK
    cX
    cY
    cvrletr.b
    cvrletr.s
    cvrletr.c
    cvrval
    @0
    @2
    @15
    @9
    wb
    @1
    @0
    @2
    wa
    #
    @14
    @8
    @3
    @16
    @14
    @7
    wn
    #
    vz
    cB
    wral
    @8
    @16
    @13
    @17
    vz
    cB
    @13
    @11
    @4
    cY
    wne
    #
    wa
    #
    wn
    @16
    @4
    cB
    wcel
    #
    wa
    #
    @17
    @13
    @11
    @12
    wn
    #
    wa
    @19
    @11
    @12
    iman
    @18
    @22
    @11
    @4
    cY
    df-ne
    anbi2i
    xchbinxr
    @21
    @19
    @7
    @21
    @7
    @5
    @10
    @18
    wa
    #
    wa
    @19
    @21
    @6
    @23
    @5
    @0
    @2
    @20
    @6
    @23
    wb
    #
    @0
    @20
    @2
    @24
    cA
    cB
    cB
    c.lt
    cK
    c.le
    @4
    cY
    cvrletr.l
    cvrletr.s
    pltval
    3com23
    3expa
    anbi2d
    @5
    @10
    @18
    anass
    syl6rbbr
    notbid
    syl5bb
    ralbidva
    @7
    vz
    cB
    ralnex
    syl6bb
    anbi2d
    3adant2
    bitr4d
end
