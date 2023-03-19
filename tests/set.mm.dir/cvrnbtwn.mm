include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "cv.mm"
include "wrex.mm"
include "wb.mm"
include "cvrval.mm"
include "3adant3r3.mm"
include "wi.mm"
include "wral.mm"
include "ralnex.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "notbid.mm"
include "rspcv.mm"
include "syl5bir.mm"
include "adantld.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "sylbid.mm"
include "3impia.mm"

theorem cvrnbtwn
  let cA: class A
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cvrfval.b: |- B = ( Base ` K )
  assume cvrfval.s: |- .< = ( lt ` K )
  assume cvrfval.c: |- C = ( <o ` K )


  assert |- ( ( K e. A /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ X C Y ) -> -. ( X .< Z /\ Z .< Y ) )

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
    cZ
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    cC
    wbr
    #
    cX
    cZ
    c.lt
    wbr
    #
    cZ
    cY
    c.lt
    wbr
    #
    wa
    #
    wn
    #
    @0
    @4
    wa
    @5
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
    @11
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
    @9
    @0
    @1
    @2
    @5
    @16
    wb
    @3
    vz
    cA
    cB
    cC
    c.lt
    cK
    cX
    cY
    cvrfval.b
    cvrfval.s
    cvrfval.c
    cvrval
    3adant3r3
    @4
    @16
    @9
    wi
    #
    @0
    @3
    @1
    @17
    @2
    @3
    @15
    @9
    @10
    @15
    @14
    wn
    #
    vz
    cB
    wral
    @3
    @9
    @14
    vz
    cB
    ralnex
    @18
    @9
    vz
    cZ
    cB
    @11
    cZ
    wceq
    #
    @14
    @8
    @19
    @12
    @6
    @13
    @7
    @11
    cZ
    cX
    c.lt
    breq2
    @11
    cZ
    cY
    c.lt
    breq1
    anbi12d
    notbid
    rspcv
    syl5bir
    adantld
    3ad2ant3
    adantl
    sylbid
    3impia
end
