include "cdom.mm"
include "wbr.mm"
include "cv.mm"
include "wf1.mm"
include "wex.mm"
include "wacn.mm"
include "wcel.mm"
include "wi.mm"
include "brdomi.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "neq0.mm"
include "w3a.mm"
include "cfv.mm"
include "wral.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "wf.mm"
include "crn.mm"
include "ccnv.mm"
include "cif.mm"
include "wss.mm"
include "wne.mm"
include "simpl3.mm"
include "elmapi.mm"
include "ad2antlr.mm"
include "wf1o.mm"
include "simpll1.mm"
include "f1f1orn.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "4syl.mm"
include "ffvelrnda.mm"
include "simpl2.mm"
include "ad2antrr.mm"
include "ifclda.mm"
include "ffvelrnd.mm"
include "eldifsn.mm"
include "elpwi.mm"
include "anim1i.mm"
include "sylbi.mm"
include "syl.mm"
include "ralrimiva.mm"
include "acni2.mm"
include "syl2anc.mm"
include "cvv.mm"
include "cdm.mm"
include "f1dm.mm"
include "vex.mm"
include "dmex.mm"
include "syl6eqelr.mm"
include "3ad2ant1.mm"
include "f1f.mm"
include "frn.mm"
include "ssralv.mm"
include "iftrue.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "ralbiia.mm"
include "syl6ib.mm"
include "wfn.mm"
include "wb.mm"
include "f1fn.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "ralrn.mm"
include "3syl.mm"
include "sylibd.mm"
include "f1ocnvfv1.mm"
include "sylan.mm"
include "ralbidva.mm"
include "impr.mm"
include "acnlem.mm"
include "exlimddv.mm"
include "elex.mm"
include "isacn.mm"
include "syl2anr.mm"
include "3adant2.mm"
include "mpbird.mm"
include "3exp.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "acneq.mm"
include "cfn.mm"
include "0fin.mm"
include "finacn.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "syl5ibr.mm"
include "pm2.61d2.mm"
include "exlimiv.mm"

theorem acndom
  let cA: class A
  let cB: class B
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cY: class Y


  assert |- ( A ~<_ B -> ( X e. AC_ B -> X e. AC_ A ) )

  proof
    cA
    cB
    cdom
    wbr
    cA
    cB
    vf
    cv
    #
    wf1
    #
    vf
    wex
    cX
    cB
    wacn
    #
    wcel
    #
    cX
    cA
    wacn
    #
    wcel
    #
    wi
    #
    cA
    cB
    vf
    brdomi
    @1
    @6
    vf
    @1
    cA
    c0
    wceq
    #
    @6
    @7
    wn
    vx
    cv
    #
    cA
    wcel
    #
    vx
    wex
    @1
    @6
    vx
    cA
    neq0
    @1
    @9
    @6
    vx
    @1
    @9
    @3
    @5
    @1
    @9
    @3
    w3a
    #
    @5
    vz
    cv
    #
    vh
    cv
    cfv
    @11
    vg
    cv
    #
    cfv
    #
    wcel
    vz
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
    cdif
    #
    cA
    cmap
    co
    #
    wral
    #
    @10
    @14
    vg
    @17
    @10
    @12
    @17
    wcel
    #
    wa
    #
    cB
    cX
    vk
    cv
    #
    wf
    #
    vy
    cv
    #
    @21
    cfv
    #
    @23
    @0
    crn
    #
    wcel
    #
    @23
    @0
    ccnv
    #
    cfv
    #
    @8
    cif
    #
    @12
    cfv
    #
    wcel
    #
    vy
    cB
    wral
    #
    wa
    #
    @14
    vk
    @20
    @3
    @30
    cX
    wss
    #
    @30
    c0
    wne
    #
    wa
    #
    vy
    cB
    wral
    @33
    vk
    wex
    @1
    @9
    @3
    @19
    simpl3
    @20
    @36
    vy
    cB
    @20
    @23
    cB
    wcel
    #
    wa
    #
    @30
    @16
    wcel
    #
    @36
    @38
    cA
    @16
    @29
    @12
    @19
    cA
    @16
    @12
    wf
    @10
    @37
    @12
    @16
    cA
    elmapi
    ad2antlr
    @38
    @26
    @28
    @8
    cA
    @38
    @25
    cA
    @23
    @27
    @38
    @1
    cA
    @25
    @0
    wf1o
    #
    @25
    cA
    @27
    wf1o
    @25
    cA
    @27
    wf
    @1
    @9
    @3
    @19
    @37
    simpll1
    cA
    cB
    @0
    f1f1orn
    #
    cA
    @25
    @0
    f1ocnv
    @25
    cA
    @27
    f1of
    4syl
    ffvelrnda
    @20
    @9
    @37
    @26
    wn
    @1
    @9
    @3
    @19
    simpl2
    ad2antrr
    ifclda
    ffvelrnd
    @39
    @30
    @15
    wcel
    #
    @35
    wa
    @36
    @30
    @15
    c0
    eldifsn
    @42
    @34
    @35
    @30
    cX
    elpwi
    anim1i
    sylbi
    syl
    ralrimiva
    vy
    cB
    @30
    vk
    cX
    acni2
    syl2anc
    @20
    @33
    wa
    cA
    cvv
    wcel
    #
    @11
    @0
    cfv
    #
    @21
    cfv
    #
    @13
    wcel
    #
    vz
    cA
    wral
    #
    @14
    @10
    @43
    @19
    @33
    @1
    @9
    @43
    @3
    @1
    cA
    @0
    cdm
    cvv
    cA
    cB
    @0
    f1dm
    @0
    vf
    vex
    dmex
    syl6eqelr
    #
    3ad2ant1
    ad2antrr
    @20
    @22
    @32
    @47
    @20
    @22
    wa
    #
    @32
    @45
    @44
    @27
    cfv
    #
    @12
    cfv
    #
    wcel
    #
    vz
    cA
    wral
    #
    @47
    @49
    @32
    @24
    @28
    @12
    cfv
    #
    wcel
    #
    vy
    @25
    wral
    #
    @53
    @49
    @32
    @31
    vy
    @25
    wral
    #
    @56
    @49
    @1
    cA
    cB
    @0
    wf
    @25
    cB
    wss
    @32
    @57
    wi
    @1
    @9
    @3
    @19
    @22
    simpll1
    #
    cA
    cB
    @0
    f1f
    cA
    cB
    @0
    frn
    @31
    vy
    @25
    cB
    ssralv
    4syl
    @31
    @55
    vy
    @25
    @26
    @30
    @54
    @24
    @26
    @29
    @28
    @12
    @26
    @28
    @8
    iftrue
    fveq2d
    eleq2d
    ralbiia
    syl6ib
    @49
    @1
    @0
    cA
    wfn
    @56
    @53
    wb
    @58
    cA
    cB
    @0
    f1fn
    @55
    @52
    vy
    vz
    cA
    @0
    @23
    @44
    wceq
    #
    @24
    @45
    @54
    @51
    @23
    @44
    @21
    fveq2
    @59
    @28
    @50
    @12
    @23
    @44
    @27
    fveq2
    fveq2d
    eleq12d
    ralrn
    3syl
    sylibd
    @49
    @52
    @46
    vz
    cA
    @49
    @11
    cA
    wcel
    #
    wa
    #
    @51
    @13
    @45
    @61
    @50
    @11
    @12
    @49
    @40
    @60
    @50
    @11
    wceq
    @49
    @1
    @40
    @58
    @41
    syl
    cA
    @25
    @11
    @0
    f1ocnvfv1
    sylan
    fveq2d
    eleq2d
    ralbidva
    sylibd
    impr
    vz
    cA
    @45
    vg
    vh
    cvv
    acnlem
    syl2anc
    exlimddv
    ralrimiva
    @1
    @3
    @5
    @18
    wb
    #
    @9
    @3
    cX
    cvv
    wcel
    #
    @43
    @62
    @1
    cX
    @2
    elex
    #
    @48
    vz
    cA
    vg
    vh
    cvv
    cvv
    cX
    isacn
    syl2anr
    3adant2
    mpbird
    3exp
    exlimdv
    syl5bi
    @3
    @5
    @7
    @63
    @64
    @7
    @4
    cvv
    cX
    @7
    @4
    c0
    wacn
    #
    cvv
    cA
    c0
    acneq
    c0
    cfn
    wcel
    @65
    cvv
    wceq
    0fin
    c0
    finacn
    ax-mp
    syl6eq
    eleq2d
    syl5ibr
    pm2.61d2
    exlimiv
    syl
end
