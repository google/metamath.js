include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "co.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "csg.mm"
include "wral.mm"
include "eqid.mm"
include "dprdssv.mm"
include "a1i.mm"
include "c0g.mm"
include "csn.mm"
include "cxp.mm"
include "cgsu.mm"
include "cfsupp.mm"
include "cixp.mm"
include "crab.mm"
include "id.mm"
include "eqidd.mm"
include "wfn.mm"
include "cvv.mm"
include "fvex.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "wa.mm"
include "wceq.mm"
include "fvconst2.mm"
include "adantl.mm"
include "dprdf.mm"
include "ffvelrnda.mm"
include "subg0cl.mm"
include "syl.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "wn.mm"
include "wnel.mm"
include "df-nel.mm"
include "dprddomprc.mm"
include "sylbir.mm"
include "con4i.mm"
include "fczfsuppd.mm"
include "dprdw.mm"
include "mpbir3and.mm"
include "eldprdi.mm"
include "ne0i.mm"
include "wrex.mm"
include "wb.mm"
include "eldprd.mm"
include "baibd.mm"
include "anbi12d.mm"
include "mpan.mm"
include "reeanv.mm"
include "cof.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "dprdfsub.mm"
include "simprd.mm"
include "simpld.mm"
include "eqeltrrd.mm"
include "oveq12.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "cgrp.mm"
include "w3a.mm"
include "dprdgrp.mm"
include "issubg4.mm"

theorem dprdsubg
  let cS: class S
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( G dom DProd S -> ( G DProd S ) e. ( SubGrp ` G ) )

  proof
    cG
    cS
    cdprd
    cdm
    wbr
    #
    cG
    cS
    cdprd
    co
    #
    cG
    csubg
    cfv
    #
    wcel
    #
    @1
    cG
    cbs
    cfv
    #
    wss
    #
    @1
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    csg
    cfv
    #
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    vx
    @1
    wral
    #
    @5
    @0
    @4
    cS
    cG
    @4
    eqid
    #
    dprdssv
    a1i
    @0
    cG
    cS
    cdm
    #
    cG
    c0g
    cfv
    #
    csn
    cxp
    #
    cgsu
    co
    #
    @1
    wcel
    @6
    @0
    cS
    vh
    vi
    @16
    cG
    @14
    vh
    cv
    @15
    cfsupp
    wbr
    vh
    vi
    @14
    vi
    cv
    cS
    cfv
    cixp
    crab
    #
    @15
    @15
    eqid
    #
    @18
    eqid
    #
    @0
    id
    #
    @0
    @14
    eqidd
    #
    @0
    @16
    @18
    wcel
    @16
    @14
    wfn
    #
    vk
    cv
    #
    @16
    cfv
    #
    @24
    cS
    cfv
    #
    wcel
    #
    vk
    @14
    wral
    @16
    @15
    cfsupp
    wbr
    @15
    cvv
    wcel
    #
    @23
    @0
    cG
    c0g
    fvex
    #
    @14
    @15
    cvv
    fnconstg
    mp1i
    @0
    @27
    vk
    @14
    @0
    @24
    @14
    wcel
    #
    wa
    #
    @25
    @15
    @26
    @30
    @25
    @15
    wceq
    @0
    @14
    @15
    @24
    @29
    fvconst2
    adantl
    @31
    @26
    @2
    wcel
    @15
    @26
    wcel
    @0
    @14
    @2
    @24
    cS
    cS
    cG
    dprdf
    ffvelrnda
    @26
    cG
    @15
    @19
    subg0cl
    syl
    eqeltrd
    ralrimiva
    @0
    @14
    cvv
    cvv
    @15
    @14
    cvv
    wcel
    #
    @0
    @32
    wn
    @14
    cvv
    wnel
    @0
    wn
    @14
    cvv
    df-nel
    cS
    cG
    dprddomprc
    sylbir
    con4i
    @28
    @0
    @29
    a1i
    fczfsuppd
    @0
    vk
    cS
    vh
    vi
    @16
    cG
    @14
    @18
    @15
    @20
    @21
    @22
    dprdw
    mpbir3and
    eldprdi
    @1
    @17
    ne0i
    syl
    @0
    @11
    vx
    vy
    @1
    @1
    @0
    @7
    @1
    wcel
    #
    @8
    @1
    wcel
    #
    wa
    #
    @7
    cG
    vf
    cv
    #
    cgsu
    co
    #
    wceq
    #
    vf
    @18
    wrex
    #
    @8
    cG
    vg
    cv
    #
    cgsu
    co
    #
    wceq
    #
    vg
    @18
    wrex
    #
    wa
    #
    @11
    @14
    @14
    wceq
    #
    @0
    @35
    @44
    wb
    @14
    eqid
    @45
    @0
    wa
    @33
    @39
    @34
    @43
    @45
    @33
    @0
    @39
    @7
    cS
    vf
    vh
    vi
    cG
    @14
    @18
    @15
    @19
    @20
    eldprd
    baibd
    @45
    @34
    @0
    @43
    @8
    cS
    vg
    vh
    vi
    cG
    @14
    @18
    @15
    @19
    @20
    eldprd
    baibd
    anbi12d
    mpan
    @44
    @38
    @42
    wa
    #
    vg
    @18
    wrex
    vf
    @18
    wrex
    @0
    @11
    @38
    @42
    vf
    vg
    @18
    @18
    reeanv
    @0
    @46
    @11
    vf
    vg
    @18
    @18
    @0
    @36
    @18
    wcel
    #
    @40
    @18
    wcel
    #
    wa
    #
    wa
    #
    @11
    @46
    @37
    @41
    @9
    co
    #
    @1
    wcel
    @50
    cG
    @36
    @40
    @9
    cof
    co
    #
    cgsu
    co
    #
    @51
    @1
    @50
    @52
    @18
    wcel
    #
    @53
    @51
    wceq
    #
    @50
    cS
    vh
    vi
    @36
    cG
    @40
    @14
    @9
    @18
    @15
    @19
    @20
    @0
    @49
    simpl
    #
    @50
    @14
    eqidd
    #
    @0
    @47
    @48
    simprl
    @0
    @47
    @48
    simprr
    @9
    eqid
    #
    dprdfsub
    #
    simprd
    @50
    cS
    vh
    vi
    @52
    cG
    @14
    @18
    @15
    @19
    @20
    @56
    @57
    @50
    @54
    @55
    @59
    simpld
    eldprdi
    eqeltrrd
    @46
    @10
    @51
    @1
    @7
    @37
    @8
    @41
    @9
    oveq12
    eleq1d
    syl5ibrcom
    rexlimdvva
    syl5bir
    sylbid
    ralrimivv
    @0
    cG
    cgrp
    wcel
    @3
    @5
    @6
    @12
    w3a
    wb
    cS
    cG
    dprdgrp
    vx
    vy
    @4
    @1
    cG
    @9
    @13
    @58
    issubg4
    syl
    mpbir3and
end
