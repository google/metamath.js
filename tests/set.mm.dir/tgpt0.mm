include "ctgp.mm"
include "wcel.mm"
include "cha.mm"
include "ct1.mm"
include "ct0.mm"
include "tgpt1.mm"
include "t1t0.mm"
include "cv.mm"
include "wb.mm"
include "wral.mm"
include "weq.mm"
include "wi.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "eleq2.mm"
include "imbi12d.mm"
include "rspccva.mm"
include "adantll.mm"
include "csg.mm"
include "co.mm"
include "cplusg.mm"
include "c0g.mm"
include "cgrp.mm"
include "wceq.mm"
include "tgpgrp.mm"
include "ad3antrrr.mm"
include "simpllr.mm"
include "simprd.mm"
include "eqid.mm"
include "grpsubid.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "simpld.mm"
include "grplid.mm"
include "eqtrd.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "ccn.mm"
include "ctmd.mm"
include "tgptmd.mm"
include "ctopon.mm"
include "tgptopon.mm"
include "cnmptc.mm"
include "cnmptid.mm"
include "ctx.mm"
include "tgpsubcn.mm"
include "cnmpt12f.mm"
include "cnmpt1plusg.mm"
include "simprl.mm"
include "cnima.mm"
include "simplr.mm"
include "grpnpcan.mm"
include "syl3anc.mm"
include "simprr.mm"
include "eqeltrd.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "mptpreima.mm"
include "elrab2.mm"
include "sylanbrc.mm"
include "rspcv.mm"
include "syl3c.mm"
include "simprbi.mm"
include "syl.mm"
include "eqeltrrd.mm"
include "expr.mm"
include "impbid.mm"
include "ralrimiva.mm"
include "ex.mm"
include "imim1d.mm"
include "ralimdvva.mm"
include "ist0-2.mm"
include "ist1-2.mm"
include "3imtr4d.mm"
include "impbid2.mm"
include "bitrd.mm"

theorem tgpt0
  let cG: class G
  let cJ: class J
  let va: setvar a
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume tgpt1.j: |- J = ( TopOpen ` G )


  assert |- ( G e. TopGrp -> ( J e. Haus <-> J e. Kol2 ) )

  proof
    cG
    ctgp
    wcel
    #
    cJ
    cha
    wcel
    cJ
    ct1
    wcel
    #
    cJ
    ct0
    wcel
    #
    cG
    cJ
    tgpt1.j
    tgpt1
    @0
    @1
    @2
    cJ
    t1t0
    @0
    vx
    cv
    #
    vz
    cv
    #
    wcel
    #
    vy
    cv
    #
    @4
    wcel
    #
    wb
    #
    vz
    cJ
    wral
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cG
    cbs
    cfv
    #
    wral
    vx
    @12
    wral
    #
    @3
    vw
    cv
    #
    wcel
    #
    @6
    @14
    wcel
    #
    wi
    #
    vw
    cJ
    wral
    #
    @10
    wi
    #
    vy
    @12
    wral
    vx
    @12
    wral
    #
    @2
    @1
    @0
    @11
    @19
    vx
    vy
    @12
    @12
    @0
    @3
    @12
    wcel
    #
    @6
    @12
    wcel
    #
    wa
    #
    wa
    #
    @18
    @9
    @10
    @24
    @18
    @9
    @24
    @18
    wa
    #
    @8
    vz
    cJ
    @25
    @4
    cJ
    wcel
    #
    wa
    @5
    @7
    @18
    @26
    @5
    @7
    wi
    #
    @24
    @17
    @27
    vw
    @4
    cJ
    vw
    vz
    weq
    @15
    @5
    @16
    @7
    @14
    @4
    @3
    eleq2
    @14
    @4
    @6
    eleq2
    imbi12d
    rspccva
    adantll
    @25
    @26
    @7
    @5
    @25
    @26
    @7
    wa
    #
    wa
    #
    @6
    @6
    cG
    csg
    cfv
    #
    co
    #
    @3
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    @4
    @29
    @33
    cG
    c0g
    cfv
    #
    @3
    @32
    co
    #
    @3
    @29
    @31
    @34
    @3
    @32
    @29
    cG
    cgrp
    wcel
    #
    @22
    @31
    @34
    wceq
    @0
    @36
    @23
    @18
    @28
    cG
    tgpgrp
    ad3antrrr
    #
    @29
    @21
    @22
    @0
    @23
    @18
    @28
    simpllr
    #
    simprd
    #
    @12
    cG
    @30
    @6
    @34
    @12
    eqid
    #
    @34
    eqid
    #
    @30
    eqid
    #
    grpsubid
    syl2anc
    oveq1d
    @29
    @36
    @21
    @35
    @3
    wceq
    @37
    @29
    @21
    @22
    @38
    simpld
    #
    @12
    @32
    cG
    @3
    @34
    @40
    @32
    eqid
    #
    @41
    grplid
    syl2anc
    eqtrd
    @29
    @6
    va
    @12
    @6
    va
    cv
    #
    @30
    co
    #
    @3
    @32
    co
    #
    cmpt
    #
    ccnv
    @4
    cima
    #
    wcel
    #
    @33
    @4
    wcel
    #
    @29
    @49
    cJ
    wcel
    #
    @18
    @3
    @49
    wcel
    #
    @50
    @29
    @48
    cJ
    cJ
    ccn
    co
    wcel
    @26
    @52
    @29
    va
    @46
    @3
    @32
    cG
    cJ
    cJ
    @12
    tgpt1.j
    @44
    @0
    cG
    ctmd
    wcel
    @23
    @18
    @28
    cG
    tgptmd
    ad3antrrr
    @0
    cJ
    @12
    ctopon
    cfv
    wcel
    #
    @23
    @18
    @28
    cG
    cJ
    @12
    tgpt1.j
    @40
    tgptopon
    #
    ad3antrrr
    #
    @29
    va
    @6
    @45
    @30
    cJ
    cJ
    cJ
    cJ
    @12
    @56
    @29
    va
    @6
    cJ
    cJ
    @12
    @12
    @56
    @56
    @39
    cnmptc
    @29
    va
    cJ
    @12
    @56
    cnmptid
    @0
    @30
    cJ
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    @23
    @18
    @28
    cG
    cJ
    @30
    tgpt1.j
    @42
    tgpsubcn
    ad3antrrr
    cnmpt12f
    @29
    va
    @3
    cJ
    cJ
    @12
    @12
    @56
    @56
    @43
    cnmptc
    cnmpt1plusg
    @25
    @26
    @7
    simprl
    @4
    @48
    cJ
    cJ
    cnima
    syl2anc
    @24
    @18
    @28
    simplr
    @29
    @21
    @6
    @3
    @30
    co
    #
    @3
    @32
    co
    #
    @4
    wcel
    #
    @53
    @43
    @29
    @58
    @6
    @4
    @29
    @36
    @22
    @21
    @58
    @6
    wceq
    @37
    @39
    @43
    @12
    @32
    cG
    @30
    @6
    @3
    @40
    @44
    @42
    grpnpcan
    syl3anc
    @25
    @26
    @7
    simprr
    eqeltrd
    @47
    @4
    wcel
    #
    @59
    va
    @3
    @12
    @49
    va
    vx
    weq
    #
    @47
    @58
    @4
    @61
    @46
    @57
    @3
    @32
    @45
    @3
    @6
    @30
    oveq2
    oveq1d
    eleq1d
    va
    @12
    @47
    @4
    @48
    @48
    eqid
    mptpreima
    #
    elrab2
    sylanbrc
    @17
    @53
    @50
    wi
    vw
    @49
    cJ
    @14
    @49
    wceq
    @15
    @53
    @16
    @50
    @14
    @49
    @3
    eleq2
    @14
    @49
    @6
    eleq2
    imbi12d
    rspcv
    syl3c
    @50
    @22
    @51
    @60
    @51
    va
    @6
    @12
    @49
    va
    vy
    weq
    #
    @47
    @33
    @4
    @63
    @46
    @31
    @3
    @32
    @45
    @6
    @6
    @30
    oveq2
    oveq1d
    eleq1d
    @62
    elrab2
    simprbi
    syl
    eqeltrrd
    expr
    impbid
    ralrimiva
    ex
    imim1d
    ralimdvva
    @0
    @54
    @2
    @13
    wb
    @55
    vx
    vy
    vz
    cJ
    @12
    ist0-2
    syl
    @0
    @54
    @1
    @20
    wb
    @55
    vx
    vy
    vw
    cJ
    @12
    ist1-2
    syl
    3imtr4d
    impbid2
    bitrd
end
