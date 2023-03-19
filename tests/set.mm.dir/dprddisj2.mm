include "cres.mm"
include "cdprd.mm"
include "co.mm"
include "cin.mm"
include "csn.mm"
include "cv.mm"
include "wcel.mm"
include "inss1.mm"
include "cdm.mm"
include "wbr.mm"
include "wss.mm"
include "dprdres.mm"
include "simprd.mm"
include "syl5ss.mm"
include "sseld.mm"
include "cgsu.mm"
include "wceq.mm"
include "cfsupp.mm"
include "cfv.mm"
include "cixp.mm"
include "crab.mm"
include "wrex.mm"
include "wa.mm"
include "wi.mm"
include "wb.mm"
include "eqid.mm"
include "eldprd.mm"
include "syl.mm"
include "cmpt.mm"
include "cbs.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "dprdff.mm"
include "feqmptd.mm"
include "cdif.mm"
include "wo.mm"
include "cun.mm"
include "c0.mm"
include "difeq2d.mm"
include "difindi.mm"
include "dif0.mm"
include "3eqtr3g.mm"
include "eqimss2.mm"
include "sselda.mm"
include "elun.mm"
include "sylib.mm"
include "simprl.mm"
include "dmdprdsplitlem.mm"
include "simprr.mm"
include "jaodan.mm"
include "syldan.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "cvv.mm"
include "cgrp.mm"
include "dprdgrp.mm"
include "grpmnd.mm"
include "3syl.mm"
include "dprddomcld.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "ex.mm"
include "eleq1.mm"
include "elin.mm"
include "syl6bb.mm"
include "velsn.mm"
include "eqeq1.mm"
include "syl5bb.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "adantld.mm"
include "sylbid.mm"
include "com23.mm"
include "mpdd.mm"
include "ssrdv.mm"
include "csubg.mm"
include "simpld.mm"
include "dprdsubg.mm"
include "subg0cl.mm"
include "elind.mm"
include "snssd.mm"
include "eqssd.mm"

theorem dprddisj2
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let cG: class G
  let cI: class I
  let c.0: class .0.
  let vf: setvar f
  let vh: setvar h
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let cZ: class Z
  assume dprdcntz2.1: |- ( ph -> G dom DProd S )
  assume dprdcntz2.2: |- ( ph -> dom S = I )
  assume dprdcntz2.c: |- ( ph -> C C_ I )
  assume dprdcntz2.d: |- ( ph -> D C_ I )
  assume dprdcntz2.i: |- ( ph -> ( C i^i D ) = (/) )
  assume dprddisj2.0: |- .0. = ( 0g ` G )


  assert |- ( ph -> ( ( G DProd ( S |` C ) ) i^i ( G DProd ( S |` D ) ) ) = { .0. } )

  proof
    wph
    cG
    cS
    cC
    cres
    #
    cdprd
    co
    #
    cG
    cS
    cD
    cres
    #
    cdprd
    co
    #
    cin
    #
    c.0
    csn
    #
    wph
    vx
    @4
    @5
    wph
    vx
    cv
    #
    @4
    wcel
    #
    @6
    cG
    cS
    cdprd
    co
    #
    wcel
    #
    @6
    @5
    wcel
    #
    wph
    @4
    @8
    @6
    wph
    @4
    @1
    @8
    @1
    @3
    inss1
    wph
    cG
    @0
    cdprd
    cdm
    #
    wbr
    #
    @1
    @8
    wss
    #
    wph
    cC
    cS
    cG
    cI
    dprdcntz2.1
    dprdcntz2.2
    dprdcntz2.c
    dprdres
    #
    simprd
    syl5ss
    sseld
    wph
    @9
    @7
    @10
    wph
    @9
    cG
    cS
    @11
    wbr
    #
    @6
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
    vh
    cv
    c.0
    cfsupp
    wbr
    vh
    vi
    cI
    vi
    cv
    cS
    cfv
    cixp
    crab
    #
    wrex
    #
    wa
    #
    @7
    @10
    wi
    #
    wph
    cS
    cdm
    cI
    wceq
    #
    @9
    @21
    wb
    dprdcntz2.2
    @6
    cS
    vf
    vh
    vi
    cG
    cI
    @19
    c.0
    dprddisj2.0
    @19
    eqid
    #
    eldprd
    syl
    wph
    @20
    @22
    @15
    wph
    @18
    @22
    vf
    @19
    wph
    @16
    @19
    wcel
    #
    wa
    #
    @22
    @18
    @17
    @1
    wcel
    #
    @17
    @3
    wcel
    #
    wa
    #
    @17
    c.0
    wceq
    #
    wi
    @26
    @29
    @30
    @26
    @29
    wa
    #
    @17
    cG
    vx
    cI
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @31
    @16
    @32
    cG
    cgsu
    @31
    @16
    vx
    cI
    @6
    @16
    cfv
    #
    cmpt
    @32
    @31
    vx
    cI
    cG
    cbs
    cfv
    #
    @16
    @31
    @35
    cS
    vh
    vi
    @16
    cG
    cI
    @19
    c.0
    @24
    wph
    @15
    @25
    @29
    dprdcntz2.1
    ad2antrr
    #
    wph
    @23
    @25
    @29
    dprdcntz2.2
    ad2antrr
    #
    wph
    @25
    @29
    simplr
    #
    @35
    eqid
    dprdff
    feqmptd
    @31
    vx
    cI
    @34
    c.0
    @31
    @6
    cI
    wcel
    #
    @6
    cI
    cC
    cdif
    #
    wcel
    #
    @6
    cI
    cD
    cdif
    #
    wcel
    #
    wo
    #
    @34
    c.0
    wceq
    #
    @31
    @39
    wa
    @6
    @40
    @42
    cun
    #
    wcel
    @44
    @31
    cI
    @46
    @6
    wph
    cI
    @46
    wss
    #
    @25
    @29
    wph
    @46
    cI
    wceq
    @47
    wph
    cI
    cC
    cD
    cin
    #
    cdif
    cI
    c0
    cdif
    @46
    cI
    wph
    @48
    c0
    cI
    dprdcntz2.i
    difeq2d
    cI
    cC
    cD
    difindi
    cI
    dif0
    3eqtr3g
    cI
    @46
    eqimss2
    syl
    ad2antrr
    sselda
    @6
    @40
    @42
    elun
    sylib
    @31
    @41
    @45
    @43
    @31
    cC
    cS
    vh
    vi
    @16
    cG
    cI
    @19
    @6
    c.0
    dprddisj2.0
    @24
    @36
    @37
    wph
    cC
    cI
    wss
    @25
    @29
    dprdcntz2.c
    ad2antrr
    @38
    @26
    @27
    @28
    simprl
    dmdprdsplitlem
    @31
    cD
    cS
    vh
    vi
    @16
    cG
    cI
    @19
    @6
    c.0
    dprddisj2.0
    @24
    @36
    @37
    wph
    cD
    cI
    wss
    @25
    @29
    dprdcntz2.d
    ad2antrr
    @38
    @26
    @27
    @28
    simprr
    dmdprdsplitlem
    jaodan
    syldan
    mpteq2dva
    eqtrd
    oveq2d
    wph
    @33
    c.0
    wceq
    #
    @25
    @29
    wph
    cG
    cmnd
    wcel
    #
    cI
    cvv
    wcel
    @49
    wph
    @15
    cG
    cgrp
    wcel
    @50
    dprdcntz2.1
    cS
    cG
    dprdgrp
    cG
    grpmnd
    3syl
    wph
    cS
    cG
    cI
    dprdcntz2.1
    dprdcntz2.2
    dprddomcld
    cI
    vx
    cG
    cvv
    c.0
    dprddisj2.0
    gsumz
    syl2anc
    ad2antrr
    eqtrd
    ex
    @18
    @7
    @29
    @10
    @30
    @18
    @7
    @17
    @4
    wcel
    @29
    @6
    @17
    @4
    eleq1
    @17
    @1
    @3
    elin
    syl6bb
    @10
    @6
    c.0
    wceq
    @18
    @30
    vx
    c.0
    velsn
    @6
    @17
    c.0
    eqeq1
    syl5bb
    imbi12d
    syl5ibrcom
    rexlimdva
    adantld
    sylbid
    com23
    mpdd
    ssrdv
    wph
    c.0
    @4
    wph
    @1
    @3
    c.0
    wph
    @12
    @1
    cG
    csubg
    cfv
    #
    wcel
    c.0
    @1
    wcel
    wph
    @12
    @13
    @14
    simpld
    @0
    cG
    dprdsubg
    @1
    cG
    c.0
    dprddisj2.0
    subg0cl
    3syl
    wph
    cG
    @2
    @11
    wbr
    #
    @3
    @51
    wcel
    c.0
    @3
    wcel
    wph
    @52
    @3
    @8
    wss
    wph
    cD
    cS
    cG
    cI
    dprdcntz2.1
    dprdcntz2.2
    dprdcntz2.d
    dprdres
    simpld
    @2
    cG
    dprdsubg
    @3
    cG
    c.0
    dprddisj2.0
    subg0cl
    3syl
    elind
    snssd
    eqssd
end
