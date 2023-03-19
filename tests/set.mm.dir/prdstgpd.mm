include "cgrp.mm"
include "wcel.mm"
include "ctmd.mm"
include "cminusg.mm"
include "cfv.mm"
include "ctopn.mm"
include "ccn.mm"
include "co.mm"
include "ctgp.mm"
include "wf.mm"
include "wss.mm"
include "cv.mm"
include "tgpgrp.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "prdsgrpd.mm"
include "tgptmd.mm"
include "prdstmdd.mm"
include "ccom.mm"
include "cpt.mm"
include "cbs.mm"
include "cmpt.mm"
include "eqid.mm"
include "grpinvf.mm"
include "syl.mm"
include "feqmptd.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "prdsinvgd.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "ctopon.mm"
include "tmdtopon.mm"
include "wfn.mm"
include "ctop.mm"
include "wral.mm"
include "cvv.mm"
include "topnfn.mm"
include "ffn.mm"
include "dffn2.mm"
include "sylib.mm"
include "fnfco.mm"
include "sylancr.mm"
include "wceq.mm"
include "fvco3.mm"
include "sylan.mm"
include "ffvelrnda.mm"
include "tgptopon.mm"
include "topontop.mm"
include "3syl.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "cuni.mm"
include "prdstopn.mm"
include "eqcomd.mm"
include "toponuni.mm"
include "mpteq1.mm"
include "ptpjcn.mm"
include "syl3anc.mm"
include "oveq12d.mm"
include "eleqtrd.mm"
include "tgpinv.mm"
include "cnmpt11f.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "ptcn.mm"
include "istgp.mm"
include "syl3anbrc.mm"

theorem prdstgpd
  let wph: wff ph
  let cR: class R
  let cS: class S
  let cI: class I
  let cV: class V
  let cW: class W
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume prdstgpd.y: |- Y = ( S Xs_ R )
  assume prdstgpd.i: |- ( ph -> I e. W )
  assume prdstgpd.s: |- ( ph -> S e. V )
  assume prdstgpd.r: |- ( ph -> R : I --> TopGrp )


  assert |- ( ph -> Y e. TopGrp )

  proof
    wph
    cY
    cgrp
    wcel
    #
    cY
    ctmd
    wcel
    #
    cY
    cminusg
    cfv
    #
    cY
    ctopn
    cfv
    #
    @3
    ccn
    co
    #
    wcel
    cY
    ctgp
    wcel
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdstgpd.y
    prdstgpd.i
    prdstgpd.s
    wph
    cI
    ctgp
    cR
    wf
    #
    ctgp
    cgrp
    wss
    cI
    cgrp
    cR
    wf
    #
    prdstgpd.r
    vx
    ctgp
    cgrp
    vx
    cv
    #
    tgpgrp
    ssriv
    cI
    ctgp
    cgrp
    cR
    fss
    sylancl
    #
    prdsgrpd
    #
    wph
    cR
    cS
    cI
    cV
    cW
    cY
    prdstgpd.y
    prdstgpd.i
    prdstgpd.s
    wph
    @5
    ctgp
    ctmd
    wss
    cI
    ctmd
    cR
    wf
    prdstgpd.r
    vx
    ctgp
    ctmd
    @7
    tgptmd
    ssriv
    cI
    ctgp
    ctmd
    cR
    fss
    sylancl
    prdstmdd
    #
    wph
    @2
    @3
    ctopn
    cR
    ccom
    #
    cpt
    cfv
    #
    ccn
    co
    #
    @4
    wph
    @2
    vx
    cY
    cbs
    cfv
    #
    vy
    cI
    vy
    cv
    #
    @7
    cfv
    #
    @15
    cR
    cfv
    #
    cminusg
    cfv
    #
    cfv
    #
    cmpt
    #
    cmpt
    #
    @13
    wph
    @2
    vx
    @14
    @7
    @2
    cfv
    #
    cmpt
    @21
    wph
    vx
    @14
    @14
    @2
    wph
    @0
    @14
    @14
    @2
    wf
    @9
    @14
    cY
    @2
    @14
    eqid
    #
    @2
    eqid
    #
    grpinvf
    syl
    feqmptd
    wph
    vx
    @14
    @22
    @20
    wph
    @7
    @14
    wcel
    #
    wa
    vy
    @14
    cR
    cS
    cI
    @2
    cV
    cW
    @7
    cY
    prdstgpd.y
    wph
    cI
    cW
    wcel
    #
    @25
    prdstgpd.i
    adantr
    wph
    cS
    cV
    wcel
    @25
    prdstgpd.s
    adantr
    wph
    @6
    @25
    @8
    adantr
    @23
    @24
    wph
    @25
    simpr
    prdsinvgd
    mpteq2dva
    eqtrd
    wph
    vx
    @19
    vy
    @11
    cI
    @3
    @12
    cW
    @14
    @12
    eqid
    #
    wph
    @1
    @3
    @14
    ctopon
    cfv
    #
    wcel
    #
    @10
    cY
    @3
    @14
    @3
    eqid
    #
    @23
    tmdtopon
    syl
    #
    prdstgpd.i
    wph
    @11
    cI
    wfn
    #
    @15
    @11
    cfv
    #
    ctop
    wcel
    #
    vy
    cI
    wral
    cI
    ctop
    @11
    wf
    #
    wph
    ctopn
    cvv
    wfn
    cI
    cvv
    cR
    wf
    #
    @32
    topnfn
    wph
    cR
    cI
    wfn
    #
    @36
    wph
    @5
    @37
    prdstgpd.r
    cI
    ctgp
    cR
    ffn
    syl
    #
    cI
    cR
    dffn2
    sylib
    cvv
    cI
    ctopn
    cR
    fnfco
    sylancr
    wph
    @34
    vy
    cI
    wph
    @15
    cI
    wcel
    #
    wa
    #
    @33
    @17
    ctopn
    cfv
    #
    ctop
    wph
    @5
    @39
    @33
    @41
    wceq
    prdstgpd.r
    cI
    ctgp
    @15
    ctopn
    cR
    fvco3
    sylan
    #
    @40
    @17
    ctgp
    wcel
    #
    @41
    @17
    cbs
    cfv
    #
    ctopon
    cfv
    wcel
    @41
    ctop
    wcel
    wph
    cI
    ctgp
    @15
    cR
    prdstgpd.r
    ffvelrnda
    #
    @17
    @41
    @44
    @41
    eqid
    #
    @44
    eqid
    tgptopon
    @44
    @41
    topontop
    3syl
    eqeltrd
    ralrimiva
    vy
    cI
    ctop
    @11
    ffnfv
    sylanbrc
    #
    @40
    vx
    @14
    @19
    cmpt
    @3
    @41
    ccn
    co
    #
    @3
    @33
    ccn
    co
    @40
    vx
    @16
    @18
    @3
    @41
    @41
    @14
    wph
    @29
    @39
    @31
    adantr
    #
    @40
    vx
    @14
    @16
    cmpt
    #
    @12
    @33
    ccn
    co
    #
    @48
    @40
    @50
    vx
    @12
    cuni
    #
    @16
    cmpt
    #
    @51
    @40
    @12
    @28
    wcel
    @14
    @52
    wceq
    @50
    @53
    wceq
    @40
    @12
    @3
    @28
    @40
    @3
    @12
    wph
    @3
    @12
    wceq
    @39
    wph
    cR
    cS
    cI
    @3
    cV
    cW
    cY
    prdstgpd.y
    prdstgpd.s
    prdstgpd.i
    @38
    @30
    prdstopn
    #
    adantr
    eqcomd
    #
    @49
    eqeltrd
    @14
    @12
    toponuni
    vx
    @14
    @52
    @16
    mpteq1
    3syl
    @40
    @26
    @35
    @39
    @53
    @51
    wcel
    wph
    @26
    @39
    prdstgpd.i
    adantr
    wph
    @35
    @39
    @47
    adantr
    wph
    @39
    simpr
    vx
    cI
    @11
    @15
    @12
    cW
    @52
    @52
    eqid
    @27
    ptpjcn
    syl3anc
    eqeltrd
    @40
    @12
    @3
    @33
    @41
    ccn
    @55
    @42
    oveq12d
    eleqtrd
    @40
    @43
    @18
    @41
    @41
    ccn
    co
    wcel
    @45
    @17
    @18
    @41
    @46
    @18
    eqid
    tgpinv
    syl
    cnmpt11f
    @40
    @33
    @41
    @3
    ccn
    @42
    oveq2d
    eleqtrrd
    ptcn
    eqeltrd
    wph
    @3
    @12
    @3
    ccn
    @54
    oveq2d
    eleqtrrd
    cY
    @2
    @3
    @30
    @24
    istgp
    syl3anbrc
end
