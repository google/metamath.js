include "wcel.mm"
include "w3a.mm"
include "ccom.mm"
include "cbs.mm"
include "cfv.mm"
include "wf1o.mm"
include "cv.mm"
include "cple.mm"
include "wbr.mm"
include "wb.mm"
include "wral.mm"
include "eqid.mm"
include "laut1o.mm"
include "3adant3.mm"
include "3adant2.mm"
include "f1oco.mm"
include "syl2anc.mm"
include "wa.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "simprl.mm"
include "lautcl.mm"
include "syl21anc.mm"
include "simprr.mm"
include "lautle.mm"
include "syl22anc.mm"
include "3adantl2.mm"
include "wf.mm"
include "wceq.mm"
include "f1of.mm"
include "syl.mm"
include "simpl.mm"
include "fvco3.mm"
include "syl2an.mm"
include "simpr.mm"
include "breq12d.mm"
include "3bitr4d.mm"
include "ralrimivva.mm"
include "islaut.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem lautco
  let cF: class F
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume lautco.i: |- I = ( LAut ` K )


  assert |- ( ( K e. V /\ F e. I /\ G e. I ) -> ( F o. G ) e. I )

  proof
    cK
    cV
    wcel
    #
    cF
    cI
    wcel
    #
    cG
    cI
    wcel
    #
    w3a
    #
    cF
    cG
    ccom
    #
    cI
    wcel
    #
    cK
    cbs
    cfv
    #
    @6
    @4
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cK
    cple
    cfv
    #
    wbr
    #
    @8
    @4
    cfv
    #
    @9
    @4
    cfv
    #
    @10
    wbr
    #
    wb
    #
    vy
    @6
    wral
    vx
    @6
    wral
    #
    @3
    @6
    @6
    cF
    wf1o
    #
    @6
    @6
    cG
    wf1o
    #
    @7
    @0
    @1
    @17
    @2
    cV
    @6
    cF
    cI
    cK
    @6
    eqid
    #
    lautco.i
    laut1o
    3adant3
    @0
    @2
    @18
    @1
    cV
    @6
    cG
    cI
    cK
    @19
    lautco.i
    laut1o
    3adant2
    #
    @6
    @6
    @6
    cF
    cG
    f1oco
    syl2anc
    @3
    @15
    vx
    vy
    @6
    @6
    @3
    @8
    @6
    wcel
    #
    @9
    @6
    wcel
    #
    wa
    #
    wa
    #
    @8
    cG
    cfv
    #
    @9
    cG
    cfv
    #
    @10
    wbr
    #
    @25
    cF
    cfv
    #
    @26
    cF
    cfv
    #
    @10
    wbr
    #
    @11
    @14
    @24
    @0
    @1
    @25
    @6
    wcel
    #
    @26
    @6
    wcel
    #
    @27
    @30
    wb
    @0
    @1
    @2
    @23
    simpl1
    #
    @0
    @1
    @2
    @23
    simpl2
    @24
    @0
    @2
    @21
    @31
    @33
    @0
    @1
    @2
    @23
    simpl3
    #
    @3
    @21
    @22
    simprl
    @6
    cG
    cI
    cK
    cV
    @8
    @19
    lautco.i
    lautcl
    syl21anc
    @24
    @0
    @2
    @22
    @32
    @33
    @34
    @3
    @21
    @22
    simprr
    @6
    cG
    cI
    cK
    cV
    @9
    @19
    lautco.i
    lautcl
    syl21anc
    @6
    cF
    cI
    cK
    @10
    cV
    @25
    @26
    @19
    @10
    eqid
    #
    lautco.i
    lautle
    syl22anc
    @0
    @2
    @23
    @11
    @27
    wb
    @1
    @6
    cG
    cI
    cK
    @10
    cV
    @8
    @9
    @19
    @35
    lautco.i
    lautle
    3adantl2
    @24
    @12
    @28
    @13
    @29
    @10
    @3
    @6
    @6
    cG
    wf
    #
    @21
    @12
    @28
    wceq
    @23
    @3
    @18
    @36
    @20
    @6
    @6
    cG
    f1of
    syl
    #
    @21
    @22
    simpl
    @6
    @6
    @8
    cF
    cG
    fvco3
    syl2an
    @3
    @36
    @22
    @13
    @29
    wceq
    @23
    @37
    @21
    @22
    simpr
    @6
    @6
    @9
    cF
    cG
    fvco3
    syl2an
    breq12d
    3bitr4d
    ralrimivva
    @0
    @1
    @5
    @7
    @16
    wa
    wb
    @2
    vx
    vy
    cV
    @6
    @4
    cI
    cK
    @10
    @19
    @35
    lautco.i
    islaut
    3ad2ant1
    mpbir2and
end
