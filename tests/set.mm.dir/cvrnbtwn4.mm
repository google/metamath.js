include "cpo.mm"
include "wcel.mm"
include "w3a.mm"
include "wbr.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "cplt.mm"
include "cfv.mm"
include "wn.mm"
include "wi.mm"
include "eqid.mm"
include "cvrnbtwn.mm"
include "wb.mm"
include "iman.mm"
include "wne.mm"
include "pltval.mm"
include "3adant3r2.mm"
include "3com23.mm"
include "3adant3r1.mm"
include "anbi12d.mm"
include "neanior.mm"
include "anbi2i.mm"
include "an4.mm"
include "bitr3i.mm"
include "syl6rbbr.mm"
include "notbid.mm"
include "syl5rbb.mm"
include "3adant3.mm"
include "mpbid.mm"
include "posref.mm"
include "3ad2antr3.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "cvrle.mm"
include "ex.mm"
include "3adant3r3.mm"
include "3impia.mm"
include "breq2.mm"
include "jaod.mm"
include "syl5ibcom.mm"
include "jcad.mm"
include "impbid.mm"

theorem cvrnbtwn4
  let cB: class B
  let cC: class C
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume cvrle.b: |- B = ( Base ` K )
  assume cvrle.l: |- .<_ = ( le ` K )
  assume cvrle.c: |- C = ( <o ` K )


  assert |- ( ( K e. Poset /\ ( X e. B /\ Y e. B /\ Z e. B ) /\ X C Y ) -> ( ( X .<_ Z /\ Z .<_ Y ) <-> ( X = Z \/ Z = Y ) ) )

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
    c.le
    wbr
    #
    cZ
    cY
    c.le
    wbr
    #
    wa
    #
    cX
    cZ
    wceq
    #
    cZ
    cY
    wceq
    #
    wo
    #
    @6
    cX
    cZ
    cK
    cplt
    cfv
    #
    wbr
    #
    cZ
    cY
    @13
    wbr
    #
    wa
    #
    wn
    #
    @9
    @12
    wi
    #
    cpo
    cB
    cC
    @13
    cK
    cX
    cY
    cZ
    cvrle.b
    @13
    eqid
    #
    cvrle.c
    cvrnbtwn
    @0
    @4
    @17
    @18
    wb
    @5
    @18
    @9
    @12
    wn
    #
    wa
    #
    wn
    @0
    @4
    wa
    #
    @17
    @9
    @12
    iman
    @22
    @21
    @16
    @22
    @16
    @7
    cX
    cZ
    wne
    #
    wa
    #
    @8
    cZ
    cY
    wne
    #
    wa
    #
    wa
    #
    @21
    @22
    @14
    @24
    @15
    @26
    @0
    @1
    @3
    @14
    @24
    wb
    @2
    cpo
    cB
    cB
    @13
    cK
    c.le
    cX
    cZ
    cvrle.l
    @19
    pltval
    3adant3r2
    @0
    @2
    @3
    @15
    @26
    wb
    #
    @1
    @0
    @3
    @2
    @28
    cpo
    cB
    cB
    @13
    cK
    c.le
    cZ
    cY
    cvrle.l
    @19
    pltval
    3com23
    3adant3r1
    anbi12d
    @21
    @9
    @23
    @25
    wa
    #
    wa
    @27
    @29
    @20
    @9
    cX
    cZ
    cZ
    cY
    neanior
    anbi2i
    @7
    @8
    @23
    @25
    an4
    bitr3i
    syl6rbbr
    notbid
    syl5rbb
    3adant3
    mpbid
    @6
    @12
    @7
    @8
    @6
    @10
    @7
    @11
    @6
    @7
    @10
    cZ
    cZ
    c.le
    wbr
    #
    @0
    @4
    @30
    @5
    @0
    @1
    @3
    @30
    @2
    cB
    cK
    c.le
    cZ
    cvrle.b
    cvrle.l
    posref
    3ad2antr3
    3adant3
    #
    cX
    cZ
    cZ
    c.le
    breq1
    syl5ibrcom
    @6
    @7
    @11
    cX
    cY
    c.le
    wbr
    #
    @0
    @4
    @5
    @32
    @0
    @1
    @2
    @5
    @32
    wi
    @3
    @0
    @1
    @2
    w3a
    @5
    @32
    cpo
    cB
    cC
    cK
    c.le
    cX
    cY
    cvrle.b
    cvrle.l
    cvrle.c
    cvrle
    ex
    3adant3r3
    3impia
    #
    cZ
    cY
    cX
    c.le
    breq2
    syl5ibrcom
    jaod
    @6
    @10
    @8
    @11
    @6
    @32
    @10
    @8
    @33
    cX
    cZ
    cY
    c.le
    breq1
    syl5ibcom
    @6
    @30
    @11
    @8
    @31
    cZ
    cY
    cZ
    c.le
    breq2
    syl5ibcom
    jaod
    jcad
    impbid
end
