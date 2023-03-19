include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wn.mm"
include "cvrnbtwn.mm"
include "3expia.mm"
include "iman.mm"
include "wne.mm"
include "wb.mm"
include "simpl.mm"
include "simpr3.mm"
include "simpr2.mm"
include "pltval.mm"
include "syl3anc.mm"
include "df-ne.mm"
include "anbi2i.mm"
include "syl6bb.mm"
include "anbi2d.mm"
include "anass.mm"
include "syl6rbbr.mm"
include "notbid.mm"
include "syl5rbb.mm"
include "sylibd.mm"
include "3impia.mm"
include "cvrlt.mm"
include "ex.mm"
include "3adant3r3.mm"
include "breq2.mm"
include "syl5ibrcom.mm"
include "posref.mm"
include "3ad2antr2.mm"
include "breq1.mm"
include "3adant3.mm"
include "jcad.mm"
include "impbid.mm"

theorem cvrnbtwn2
  let cB: class B
  let cC: class C
  let c.lt: class .<
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let cA: class A
  let vz: setvar z
  assume cvrletr.b: |- B = ( Base ` K )
  assume cvrletr.l: |- .<_ = ( le ` K )
  assume cvrletr.s: |- .< = ( lt ` K )
  assume cvrletr.c: |- C = ( <o ` K )


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ X C Y ) -> ( ( X .< Z /\ Z .<_ Y ) <-> Z = Y ) )

  proof
    cK
    cpo
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
    w3a
    #
    cX
    cZ
    c.lt
    wbr
    #
    cZ
    cY
    c.le
    wbr
    #
    wa
    #
    cZ
    cY
    wceq
    #
    @0
    @4
    @5
    @9
    @10
    wi
    #
    @0
    @4
    wa
    #
    @5
    @7
    cZ
    cY
    c.lt
    wbr
    #
    wa
    #
    wn
    #
    @11
    @0
    @4
    @5
    @15
    cpo
    cB
    cC
    c.lt
    cK
    cX
    cY
    cZ
    cvrletr.b
    cvrletr.s
    cvrletr.c
    cvrnbtwn
    3expia
    @11
    @9
    @10
    wn
    #
    wa
    #
    wn
    @12
    @15
    @9
    @10
    iman
    @12
    @17
    @14
    @12
    @14
    @7
    @8
    @16
    wa
    #
    wa
    @17
    @12
    @13
    @18
    @7
    @12
    @13
    @8
    cZ
    cY
    wne
    #
    wa
    #
    @18
    @12
    @0
    @3
    @2
    @13
    @20
    wb
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr3
    @0
    @1
    @2
    @3
    simpr2
    cpo
    cB
    cB
    c.lt
    cK
    c.le
    cZ
    cY
    cvrletr.l
    cvrletr.s
    pltval
    syl3anc
    @19
    @16
    @8
    cZ
    cY
    df-ne
    anbi2i
    syl6bb
    anbi2d
    @7
    @8
    @16
    anass
    syl6rbbr
    notbid
    syl5rbb
    sylibd
    3impia
    @6
    @10
    @7
    @8
    @6
    @7
    @10
    cX
    cY
    c.lt
    wbr
    #
    @0
    @4
    @5
    @21
    @0
    @1
    @2
    @5
    @21
    wi
    @3
    @0
    @1
    @2
    w3a
    @5
    @21
    cpo
    cB
    cC
    c.lt
    cK
    cX
    cY
    cvrletr.b
    cvrletr.s
    cvrletr.c
    cvrlt
    ex
    3adant3r3
    3impia
    cZ
    cY
    cX
    c.lt
    breq2
    syl5ibrcom
    @0
    @4
    @10
    @8
    wi
    @5
    @12
    @8
    @10
    cY
    cY
    c.le
    wbr
    #
    @0
    @1
    @2
    @22
    @3
    cB
    cK
    c.le
    cY
    cvrletr.b
    cvrletr.l
    posref
    3ad2antr2
    cZ
    cY
    cY
    c.le
    breq1
    syl5ibrcom
    3adant3
    jcad
    impbid
end
