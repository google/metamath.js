include "ctgp.mm"
include "wcel.mm"
include "cha.mm"
include "csn.mm"
include "ccld.mm"
include "cfv.mm"
include "cuni.mm"
include "wi.mm"
include "cbs.mm"
include "cgrp.mm"
include "tgpgrp.mm"
include "eqid.mm"
include "grpidcl.mm"
include "syl.mm"
include "ctopon.mm"
include "wceq.mm"
include "tgptopon.mm"
include "toponuni.mm"
include "eleqtrd.mm"
include "sncld.mm"
include "expcom.mm"
include "cid.mm"
include "cres.mm"
include "ctx.mm"
include "co.mm"
include "csg.mm"
include "ccnv.mm"
include "cima.mm"
include "ccn.mm"
include "tgpsubcn.mm"
include "cnclima.mm"
include "ex.mm"
include "cv.mm"
include "wbr.mm"
include "copab.mm"
include "wrel.mm"
include "cxp.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "grpsubf.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "dfrel4v.mm"
include "sylib.mm"
include "wa.mm"
include "cop.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "opelxp.mm"
include "anbi1i.mm"
include "grpsubeq0.mm"
include "3expb.mm"
include "sylan.mm"
include "df-ov.mm"
include "eleq1i.mm"
include "ovex.mm"
include "elsn.mm"
include "bitr3i.mm"
include "equcom.mm"
include "3bitr4g.mm"
include "pm5.32da.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "df-br.mm"
include "eleq1.mm"
include "biimparc.mm"
include "pm4.71i.mm"
include "an32.mm"
include "bitr4i.mm"
include "opabbidv.mm"
include "opabresid.mm"
include "syl6eq.mm"
include "reseq2d.mm"
include "3eqtrd.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "ctop.mm"
include "topontop.mm"
include "hausdiag.mm"
include "baib.mm"
include "sylibrd.mm"
include "impbid.mm"

theorem tgphaus
  let cG: class G
  let cJ: class J
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume tgphaus.1: |- .0. = ( 0g ` G )
  assume tgphaus.j: |- J = ( TopOpen ` G )


  assert |- ( G e. TopGrp -> ( J e. Haus <-> { .0. } e. ( Clsd ` J ) ) )

  proof
    cG
    ctgp
    wcel
    #
    cJ
    cha
    wcel
    #
    c.0
    csn
    #
    cJ
    ccld
    cfv
    wcel
    #
    @0
    c.0
    cJ
    cuni
    #
    wcel
    #
    @1
    @3
    wi
    @0
    c.0
    cG
    cbs
    cfv
    #
    @4
    @0
    cG
    cgrp
    wcel
    #
    c.0
    @6
    wcel
    cG
    tgpgrp
    #
    @6
    cG
    c.0
    @6
    eqid
    #
    tgphaus.1
    grpidcl
    syl
    @0
    cJ
    @6
    ctopon
    cfv
    wcel
    #
    @6
    @4
    wceq
    cG
    cJ
    @6
    tgphaus.j
    @9
    tgptopon
    #
    @6
    cJ
    toponuni
    syl
    #
    eleqtrd
    @1
    @5
    @3
    c.0
    cJ
    @4
    @4
    eqid
    #
    sncld
    expcom
    syl
    @0
    @3
    cid
    @4
    cres
    #
    cJ
    cJ
    ctx
    co
    #
    ccld
    cfv
    #
    wcel
    #
    @1
    @0
    @3
    cG
    csg
    cfv
    #
    ccnv
    @2
    cima
    #
    @16
    wcel
    #
    @17
    @0
    @18
    @15
    cJ
    ccn
    co
    wcel
    #
    @3
    @20
    wi
    cG
    cJ
    @18
    tgphaus.j
    @18
    eqid
    #
    tgpsubcn
    @21
    @3
    @20
    @2
    @18
    @15
    cJ
    cnclima
    ex
    syl
    @0
    @19
    @14
    @16
    @0
    @19
    vx
    cv
    #
    vy
    cv
    #
    @19
    wbr
    #
    vx
    vy
    copab
    #
    cid
    @6
    cres
    #
    @14
    @0
    @19
    wrel
    #
    @19
    @26
    wceq
    @0
    @19
    @6
    @6
    cxp
    #
    wss
    @29
    wrel
    @28
    @0
    @18
    cdm
    #
    @19
    @29
    @18
    @2
    cnvimass
    @0
    @29
    @6
    @18
    wf
    #
    @30
    @29
    wceq
    @0
    @7
    @31
    @8
    @6
    cG
    @18
    @9
    @22
    grpsubf
    syl
    #
    @29
    @6
    @18
    fdm
    syl
    syl5sseq
    @6
    @6
    relxp
    @19
    @29
    relss
    mpisyl
    vx
    vy
    @19
    dfrel4v
    sylib
    @0
    @26
    @23
    @6
    wcel
    #
    @24
    @23
    wceq
    #
    wa
    #
    vx
    vy
    copab
    @27
    @0
    @25
    @35
    vx
    vy
    @0
    @23
    @24
    cop
    #
    @19
    wcel
    #
    @33
    @24
    @6
    wcel
    #
    wa
    #
    @34
    wa
    #
    @25
    @35
    @0
    @37
    @36
    @29
    wcel
    #
    @36
    @18
    cfv
    #
    @2
    wcel
    #
    wa
    #
    @40
    @0
    @18
    @29
    wfn
    #
    @37
    @44
    wb
    @0
    @31
    @45
    @32
    @29
    @6
    @18
    ffn
    syl
    @29
    @36
    @2
    @18
    elpreima
    syl
    @44
    @39
    @43
    wa
    @0
    @40
    @41
    @39
    @43
    @23
    @24
    @6
    @6
    opelxp
    anbi1i
    @0
    @39
    @43
    @34
    @0
    @39
    wa
    @23
    @24
    @18
    co
    #
    c.0
    wceq
    #
    @23
    @24
    wceq
    #
    @43
    @34
    @0
    @7
    @39
    @47
    @48
    wb
    #
    @8
    @7
    @33
    @38
    @49
    @6
    cG
    @18
    @23
    @24
    c.0
    @9
    tgphaus.1
    @22
    grpsubeq0
    3expb
    sylan
    @43
    @46
    @2
    wcel
    @47
    @46
    @42
    @2
    @23
    @24
    @18
    df-ov
    eleq1i
    @46
    c.0
    @23
    @24
    @18
    ovex
    elsn
    bitr3i
    vy
    vx
    equcom
    3bitr4g
    pm5.32da
    syl5bb
    bitrd
    @23
    @24
    @19
    df-br
    @35
    @35
    @38
    wa
    @40
    @35
    @38
    @34
    @38
    @33
    @24
    @23
    @6
    eleq1
    biimparc
    pm4.71i
    @33
    @38
    @34
    an32
    bitr4i
    3bitr4g
    opabbidv
    vx
    vy
    @6
    opabresid
    syl6eq
    @0
    @6
    @4
    cid
    @12
    reseq2d
    3eqtrd
    eleq1d
    sylibd
    @0
    cJ
    ctop
    wcel
    #
    @1
    @17
    wb
    @0
    @10
    @50
    @11
    @6
    cJ
    topontop
    syl
    @1
    @50
    @17
    cJ
    @4
    @13
    hausdiag
    baib
    syl
    sylibrd
    impbid
end
