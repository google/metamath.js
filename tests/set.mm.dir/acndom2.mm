include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "wacn.mm"
include "wcel.mm"
include "wi.mm"
include "brdomi.mm"
include "wa.mm"
include "cfv.mm"
include "wral.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cmap.mm"
include "co.mm"
include "wf.mm"
include "cima.mm"
include "wss.mm"
include "wne.mm"
include "simplr.mm"
include "crn.mm"
include "imassrn.mm"
include "simplll.mm"
include "f1f.mm"
include "frn.mm"
include "3syl.mm"
include "syl5ss.mm"
include "cdm.mm"
include "cin.mm"
include "wceq.mm"
include "elmapi.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "eldifad.mm"
include "elpwid.mm"
include "f1dm.mm"
include "syl.mm"
include "sseqtr4d.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eldifsni.mm"
include "eqnetrd.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "sylibr.mm"
include "jca.mm"
include "ralrimiva.mm"
include "acni2.mm"
include "syl2anc.mm"
include "cvv.mm"
include "ccnv.mm"
include "acnrcl.mm"
include "ad3antlr.mm"
include "wf1o.mm"
include "simp-4l.mm"
include "f1f1orn.mm"
include "simprr.mm"
include "sseldi.mm"
include "f1ocnvfv2.mm"
include "eqeltrd.mm"
include "wb.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "ffvelrnd.mm"
include "ad2ant2r.mm"
include "f1elima.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "expr.mm"
include "ralimdva.mm"
include "impr.mm"
include "acnlem.mm"
include "exlimddv.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "isacn.mm"
include "syl2an.mm"
include "mpbird.mm"
include "ex.mm"
include "exlimiv.mm"

theorem acndom2
  let cA: class A
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( X ~<_ Y -> ( Y e. AC_ A -> X e. AC_ A ) )

  proof
    cX
    cY
    cdom
    wbr
    cX
    cY
    vf
    cv
    #
    wf1
    #
    vf
    wex
    cY
    cA
    wacn
    #
    wcel
    #
    cX
    @2
    wcel
    #
    wi
    #
    cX
    cY
    vf
    brdomi
    @1
    @5
    vf
    @1
    @3
    @4
    @1
    @3
    wa
    #
    @4
    vx
    cv
    #
    vh
    cv
    cfv
    @7
    vg
    cv
    #
    cfv
    #
    wcel
    vx
    cA
    wral
    vh
    wex
    #
    vg
    cX
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cA
    cmap
    co
    #
    wral
    #
    @6
    @10
    vg
    @14
    @6
    @8
    @14
    wcel
    #
    wa
    #
    cA
    cY
    vk
    cv
    #
    wf
    #
    @7
    @18
    cfv
    #
    @0
    @9
    cima
    #
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    @10
    vk
    @17
    @3
    @21
    cY
    wss
    #
    @21
    c0
    wne
    #
    wa
    #
    vx
    cA
    wral
    @24
    vk
    wex
    @1
    @3
    @16
    simplr
    @17
    @27
    vx
    cA
    @17
    @7
    cA
    wcel
    #
    wa
    #
    @25
    @26
    @29
    @21
    @0
    crn
    #
    cY
    @0
    @9
    imassrn
    #
    @29
    @1
    cX
    cY
    @0
    wf
    @30
    cY
    wss
    @1
    @3
    @16
    @28
    simplll
    #
    cX
    cY
    @0
    f1f
    cX
    cY
    @0
    frn
    3syl
    syl5ss
    @29
    @0
    cdm
    #
    @9
    cin
    #
    c0
    wne
    @26
    @29
    @34
    @9
    c0
    @29
    @9
    @33
    wss
    @34
    @9
    wceq
    @29
    @9
    cX
    @33
    @29
    @9
    cX
    @29
    @9
    @11
    @12
    @17
    cA
    @13
    @7
    @8
    @16
    cA
    @13
    @8
    wf
    @6
    @8
    @13
    cA
    elmapi
    adantl
    ffvelrnda
    #
    eldifad
    elpwid
    #
    @29
    @1
    @33
    cX
    wceq
    @32
    cX
    cY
    @0
    f1dm
    #
    syl
    sseqtr4d
    @9
    @33
    sseqin2
    sylib
    @29
    @9
    @13
    wcel
    @9
    c0
    wne
    @35
    @9
    @11
    c0
    eldifsni
    syl
    eqnetrd
    @21
    c0
    @34
    c0
    @0
    @9
    imadisj
    necon3bii
    sylibr
    jca
    ralrimiva
    vx
    cA
    @21
    vk
    cY
    acni2
    syl2anc
    @17
    @24
    wa
    cA
    cvv
    wcel
    #
    @20
    @0
    ccnv
    #
    cfv
    #
    @9
    wcel
    #
    vx
    cA
    wral
    #
    @10
    @3
    @38
    @1
    @16
    @24
    cA
    cY
    acnrcl
    #
    ad3antlr
    @17
    @19
    @23
    @42
    @17
    @19
    wa
    #
    @22
    @41
    vx
    cA
    @44
    @28
    @22
    @41
    @44
    @28
    @22
    wa
    #
    wa
    #
    @40
    @0
    cfv
    #
    @21
    wcel
    #
    @41
    @46
    @47
    @20
    @21
    @46
    cX
    @30
    @0
    wf1o
    #
    @20
    @30
    wcel
    @47
    @20
    wceq
    @46
    @1
    @49
    @1
    @3
    @16
    @19
    @45
    simp-4l
    #
    cX
    cY
    @0
    f1f1orn
    syl
    #
    @46
    @21
    @30
    @20
    @31
    @44
    @28
    @22
    simprr
    #
    sseldi
    #
    cX
    @30
    @20
    @0
    f1ocnvfv2
    syl2anc
    @52
    eqeltrd
    @46
    @1
    @40
    cX
    wcel
    @9
    cX
    wss
    #
    @48
    @41
    wb
    @50
    @46
    @30
    cX
    @20
    @39
    @46
    @49
    @30
    cX
    @39
    wf1o
    @30
    cX
    @39
    wf
    @51
    cX
    @30
    @0
    f1ocnv
    @30
    cX
    @39
    f1of
    3syl
    @53
    ffvelrnd
    @17
    @28
    @54
    @19
    @22
    @36
    ad2ant2r
    cX
    cY
    @0
    @40
    @9
    f1elima
    syl3anc
    mpbid
    expr
    ralimdva
    impr
    vx
    cA
    @40
    vg
    vh
    cvv
    acnlem
    syl2anc
    exlimddv
    ralrimiva
    @1
    cX
    cvv
    wcel
    @38
    @4
    @15
    wb
    @3
    @1
    cX
    @33
    cvv
    @37
    @0
    vf
    vex
    dmex
    syl6eqelr
    @43
    vx
    cA
    vg
    vh
    cvv
    cvv
    cX
    isacn
    syl2an
    mpbird
    ex
    exlimiv
    syl
end
