include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cplt.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wn.mm"
include "eqid.mm"
include "lautlt.mm"
include "wb.mm"
include "simpll.mm"
include "simplr1.mm"
include "simplr2.mm"
include "simpr.mm"
include "syl13anc.mm"
include "simplr3.mm"
include "anbi12d.mm"
include "wi.mm"
include "lautcl.mm"
include "syl21anc.mm"
include "wceq.mm"
include "breq2.mm"
include "breq1.mm"
include "rspcev.mm"
include "ex.mm"
include "syl.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "ccnv.mm"
include "wf1o.mm"
include "laut1o.mm"
include "syl2anc.mm"
include "f1ocnvdm.mm"
include "sylancom.mm"
include "f1ocnvfv2.mm"
include "breq2d.mm"
include "bitr2d.mm"
include "breq1d.mm"
include "impbid.mm"
include "notbid.mm"
include "cvrval.mm"
include "3adant3r1.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "syl3anc.mm"
include "3bitr4d.mm"

theorem lautcvr
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cI: class I
  let cK: class K
  let cX: class X
  let cY: class Y
  let vw: setvar w
  let vz: setvar z
  assume lautcvr.b: |- B = ( Base ` K )
  assume lautcvr.c: |- C = ( <o ` K )
  assume lautcvr.i: |- I = ( LAut ` K )


  assert |- ( ( K e. A /\ ( F e. I /\ X e. B /\ Y e. B ) ) -> ( X C Y <-> ( F ` X ) C ( F ` Y ) ) )

  proof
    cK
    cA
    wcel
    #
    cF
    cI
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
    wa
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
    vw
    cv
    #
    @6
    wbr
    #
    @8
    cY
    @6
    wbr
    #
    wa
    #
    vw
    cB
    wrex
    #
    wn
    #
    wa
    #
    cX
    cF
    cfv
    #
    cY
    cF
    cfv
    #
    @6
    wbr
    #
    @15
    vz
    cv
    #
    @6
    wbr
    #
    @18
    @16
    @6
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
    cX
    cY
    cC
    wbr
    #
    @15
    @16
    cC
    wbr
    #
    @5
    @7
    @17
    @13
    @23
    cA
    cB
    @6
    cF
    cI
    cK
    cX
    cY
    lautcvr.b
    @6
    eqid
    #
    lautcvr.i
    lautlt
    @5
    @12
    @22
    @5
    @12
    @22
    @5
    @11
    @22
    vw
    cB
    @5
    @8
    cB
    wcel
    #
    wa
    #
    @11
    @15
    @8
    cF
    cfv
    #
    @6
    wbr
    #
    @30
    @16
    @6
    wbr
    #
    wa
    #
    @22
    @29
    @9
    @31
    @10
    @32
    @29
    @0
    @1
    @2
    @28
    @9
    @31
    wb
    @0
    @4
    @28
    simpll
    #
    @1
    @2
    @3
    @0
    @28
    simplr1
    #
    @1
    @2
    @3
    @0
    @28
    simplr2
    @5
    @28
    simpr
    #
    cA
    cB
    @6
    cF
    cI
    cK
    cX
    @8
    lautcvr.b
    @27
    lautcvr.i
    lautlt
    syl13anc
    @29
    @0
    @1
    @28
    @3
    @10
    @32
    wb
    @34
    @35
    @36
    @1
    @2
    @3
    @0
    @28
    simplr3
    cA
    cB
    @6
    cF
    cI
    cK
    @8
    cY
    lautcvr.b
    @27
    lautcvr.i
    lautlt
    syl13anc
    anbi12d
    @29
    @30
    cB
    wcel
    #
    @33
    @22
    wi
    @29
    @0
    @1
    @28
    @37
    @34
    @35
    @36
    cB
    cF
    cI
    cK
    cA
    @8
    lautcvr.b
    lautcvr.i
    lautcl
    syl21anc
    @37
    @33
    @22
    @21
    @33
    vz
    @30
    cB
    @18
    @30
    wceq
    @19
    @31
    @20
    @32
    @18
    @30
    @15
    @6
    breq2
    @18
    @30
    @16
    @6
    breq1
    anbi12d
    rspcev
    ex
    syl
    sylbid
    rexlimdva
    @5
    @21
    @12
    vz
    cB
    @5
    @18
    cB
    wcel
    #
    wa
    #
    @21
    cX
    @18
    cF
    ccnv
    cfv
    #
    @6
    wbr
    #
    @40
    cY
    @6
    wbr
    #
    wa
    #
    @12
    @39
    @19
    @41
    @20
    @42
    @39
    @41
    @15
    @40
    cF
    cfv
    #
    @6
    wbr
    #
    @19
    @39
    @0
    @1
    @2
    @40
    cB
    wcel
    #
    @41
    @45
    wb
    @0
    @4
    @38
    simpll
    #
    @1
    @2
    @3
    @0
    @38
    simplr1
    #
    @1
    @2
    @3
    @0
    @38
    simplr2
    @5
    @38
    cB
    cB
    cF
    wf1o
    #
    @46
    @39
    @0
    @1
    @49
    @47
    @48
    cA
    cB
    cF
    cI
    cK
    lautcvr.b
    lautcvr.i
    laut1o
    syl2anc
    #
    cB
    cB
    @18
    cF
    f1ocnvdm
    sylancom
    #
    cA
    cB
    @6
    cF
    cI
    cK
    cX
    @40
    lautcvr.b
    @27
    lautcvr.i
    lautlt
    syl13anc
    @39
    @44
    @18
    @15
    @6
    @5
    @38
    @49
    @44
    @18
    wceq
    @50
    cB
    cB
    @18
    cF
    f1ocnvfv2
    sylancom
    #
    breq2d
    bitr2d
    @39
    @42
    @44
    @16
    @6
    wbr
    #
    @20
    @39
    @0
    @1
    @46
    @3
    @42
    @53
    wb
    @47
    @48
    @51
    @1
    @2
    @3
    @0
    @38
    simplr3
    cA
    cB
    @6
    cF
    cI
    cK
    @40
    cY
    lautcvr.b
    @27
    lautcvr.i
    lautlt
    syl13anc
    @39
    @44
    @18
    @16
    @6
    @52
    breq1d
    bitr2d
    anbi12d
    @39
    @46
    @43
    @12
    wi
    @51
    @46
    @43
    @12
    @11
    @43
    vw
    @40
    cB
    @8
    @40
    wceq
    @9
    @41
    @10
    @42
    @8
    @40
    cX
    @6
    breq2
    @8
    @40
    cY
    @6
    breq1
    anbi12d
    rspcev
    ex
    syl
    sylbid
    rexlimdva
    impbid
    notbid
    anbi12d
    @0
    @2
    @3
    @25
    @14
    wb
    @1
    vw
    cA
    cB
    cC
    @6
    cK
    cX
    cY
    lautcvr.b
    @27
    lautcvr.c
    cvrval
    3adant3r1
    @5
    @0
    @15
    cB
    wcel
    #
    @16
    cB
    wcel
    #
    @26
    @24
    wb
    @0
    @4
    simpl
    #
    @5
    @0
    @1
    @2
    @54
    @56
    @0
    @1
    @2
    @3
    simpr1
    #
    @0
    @1
    @2
    @3
    simpr2
    cB
    cF
    cI
    cK
    cA
    cX
    lautcvr.b
    lautcvr.i
    lautcl
    syl21anc
    @5
    @0
    @1
    @3
    @55
    @56
    @57
    @0
    @1
    @2
    @3
    simpr3
    cB
    cF
    cI
    cK
    cA
    cY
    lautcvr.b
    lautcvr.i
    lautcl
    syl21anc
    vz
    cA
    cB
    cC
    @6
    cK
    @15
    @16
    lautcvr.b
    @27
    lautcvr.c
    cvrval
    syl3anc
    3bitr4d
end
