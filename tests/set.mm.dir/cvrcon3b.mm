include "cops.mm"
include "wcel.mm"
include "w3a.mm"
include "cplt.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wn.mm"
include "eqid.mm"
include "opltcon3b.mm"
include "wb.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpr.mm"
include "syl3anc.mm"
include "simpl3.mm"
include "anbi12d.mm"
include "wi.mm"
include "opoccl.mm"
include "3ad2antl1.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "rspcev.mm"
include "ex.mm"
include "syl.mm"
include "ancomsd.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "opltcon1b.mm"
include "opltcon2b.mm"
include "impbid.mm"
include "notbid.mm"
include "cvrval.mm"
include "simp1.mm"
include "3adant2.mm"
include "3adant3.mm"
include "3bitr4d.mm"

theorem cvrcon3b
  let cB: class B
  let cC: class C
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume cvrcon3b.b: |- B = ( Base ` K )
  assume cvrcon3b.o: |- ._|_ = ( oc ` K )
  assume cvrcon3b.c: |- C = ( <o ` K )


  assert |- ( ( K e. OP /\ X e. B /\ Y e. B ) -> ( X C Y <-> ( ._|_ ` Y ) C ( ._|_ ` X ) ) )

  proof
    cK
    cops
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
    #
    cX
    cY
    cK
    cplt
    cfv
    #
    wbr
    #
    cX
    vx
    cv
    #
    @4
    wbr
    #
    @6
    cY
    @4
    wbr
    #
    wa
    #
    vx
    cB
    wrex
    #
    wn
    #
    wa
    cY
    c.pe
    cfv
    #
    cX
    c.pe
    cfv
    #
    @4
    wbr
    #
    @12
    vy
    cv
    #
    @4
    wbr
    #
    @15
    @13
    @4
    wbr
    #
    wa
    #
    vy
    cB
    wrex
    #
    wn
    #
    wa
    #
    cX
    cY
    cC
    wbr
    @12
    @13
    cC
    wbr
    #
    @3
    @5
    @14
    @11
    @20
    cB
    @4
    cK
    c.pe
    cX
    cY
    cvrcon3b.b
    @4
    eqid
    #
    cvrcon3b.o
    opltcon3b
    @3
    @10
    @19
    @3
    @10
    @19
    @3
    @9
    @19
    vx
    cB
    @3
    @6
    cB
    wcel
    #
    wa
    #
    @9
    @6
    c.pe
    cfv
    #
    @13
    @4
    wbr
    #
    @12
    @26
    @4
    wbr
    #
    wa
    @19
    @25
    @7
    @27
    @8
    @28
    @25
    @0
    @1
    @24
    @7
    @27
    wb
    @0
    @1
    @2
    @24
    simpl1
    #
    @0
    @1
    @2
    @24
    simpl2
    @3
    @24
    simpr
    #
    cB
    @4
    cK
    c.pe
    cX
    @6
    cvrcon3b.b
    @23
    cvrcon3b.o
    opltcon3b
    syl3anc
    @25
    @0
    @24
    @2
    @8
    @28
    wb
    @29
    @30
    @0
    @1
    @2
    @24
    simpl3
    cB
    @4
    cK
    c.pe
    @6
    cY
    cvrcon3b.b
    @23
    cvrcon3b.o
    opltcon3b
    syl3anc
    anbi12d
    @25
    @28
    @27
    @19
    @25
    @26
    cB
    wcel
    #
    @28
    @27
    wa
    #
    @19
    wi
    @0
    @1
    @24
    @31
    @2
    cB
    cK
    c.pe
    @6
    cvrcon3b.b
    cvrcon3b.o
    opoccl
    3ad2antl1
    @31
    @32
    @19
    @18
    @32
    vy
    @26
    cB
    @15
    @26
    wceq
    @16
    @28
    @17
    @27
    @15
    @26
    @12
    @4
    breq2
    @15
    @26
    @13
    @4
    breq1
    anbi12d
    rspcev
    ex
    syl
    ancomsd
    sylbid
    rexlimdva
    @3
    @18
    @10
    vy
    cB
    @3
    @15
    cB
    wcel
    #
    wa
    #
    @18
    @15
    c.pe
    cfv
    #
    cY
    @4
    wbr
    #
    cX
    @35
    @4
    wbr
    #
    wa
    @10
    @34
    @16
    @36
    @17
    @37
    @34
    @0
    @2
    @33
    @16
    @36
    wb
    @0
    @1
    @2
    @33
    simpl1
    #
    @0
    @1
    @2
    @33
    simpl3
    @3
    @33
    simpr
    #
    cB
    @4
    cK
    c.pe
    cY
    @15
    cvrcon3b.b
    @23
    cvrcon3b.o
    opltcon1b
    syl3anc
    @34
    @0
    @33
    @1
    @17
    @37
    wb
    @38
    @39
    @0
    @1
    @2
    @33
    simpl2
    cB
    @4
    cK
    c.pe
    @15
    cX
    cvrcon3b.b
    @23
    cvrcon3b.o
    opltcon2b
    syl3anc
    anbi12d
    @34
    @37
    @36
    @10
    @34
    @35
    cB
    wcel
    #
    @37
    @36
    wa
    #
    @10
    wi
    @0
    @1
    @33
    @40
    @2
    cB
    cK
    c.pe
    @15
    cvrcon3b.b
    cvrcon3b.o
    opoccl
    3ad2antl1
    @40
    @41
    @10
    @9
    @41
    vx
    @35
    cB
    @6
    @35
    wceq
    @7
    @37
    @8
    @36
    @6
    @35
    cX
    @4
    breq2
    @6
    @35
    cY
    @4
    breq1
    anbi12d
    rspcev
    ex
    syl
    ancomsd
    sylbid
    rexlimdva
    impbid
    notbid
    anbi12d
    vx
    cops
    cB
    cC
    @4
    cK
    cX
    cY
    cvrcon3b.b
    @23
    cvrcon3b.c
    cvrval
    @3
    @0
    @12
    cB
    wcel
    #
    @13
    cB
    wcel
    #
    @22
    @21
    wb
    @0
    @1
    @2
    simp1
    @0
    @2
    @42
    @1
    cB
    cK
    c.pe
    cY
    cvrcon3b.b
    cvrcon3b.o
    opoccl
    3adant2
    @0
    @1
    @43
    @2
    cB
    cK
    c.pe
    cX
    cvrcon3b.b
    cvrcon3b.o
    opoccl
    3adant3
    vy
    cops
    cB
    cC
    @4
    cK
    @12
    @13
    cvrcon3b.b
    @23
    cvrcon3b.c
    cvrval
    syl3anc
    3bitr4d
end
