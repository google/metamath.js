include "char.mm"
include "cfv.mm"
include "cun.mm"
include "cbs.mm"
include "cgrp.mm"
include "cima.mm"
include "wcel.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "wfn.mm"
include "wss.mm"
include "wb.mm"
include "basfn.mm"
include "ssv.mm"
include "fvelimab.mm"
include "mp2an.mm"
include "wa.mm"
include "cxp.mm"
include "cdom.mm"
include "wbr.mm"
include "con0.mm"
include "harcl.mm"
include "onenon.mm"
include "ax-mp.mm"
include "xpnum.mm"
include "cwdom.mm"
include "cplusg.mm"
include "ssun1.mm"
include "simpr.mm"
include "syl5sseqr.mm"
include "fvex.mm"
include "ssex.mm"
include "syl.mm"
include "a1i.mm"
include "w3a.mm"
include "co.mm"
include "simp1l.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "sseldd.mm"
include "ssun2.mm"
include "simp3.mm"
include "eqid.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "simp1r.mm"
include "eleqtrd.mm"
include "simplll.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "simprr.mm"
include "simplr.mm"
include "grplcan.mm"
include "syl13anc.mm"
include "grprcan.mm"
include "wn.mm"
include "harndom.mm"
include "unxpwdom3.mm"
include "wdomnumr.mm"
include "sylib.mm"
include "numdom.mm"
include "sylancr.mm"
include "rexlimiva.mm"
include "sylbi.mm"

theorem isnumbasgrplem2
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vx: setvar x


  assert |- ( ( S u. ( har ` S ) ) e. ( Base " Grp ) -> S e. dom card )

  proof
    cS
    cS
    char
    cfv
    #
    cun
    #
    cbs
    cgrp
    cima
    wcel
    #
    vx
    cv
    #
    cbs
    cfv
    #
    @1
    wceq
    #
    vx
    cgrp
    wrex
    #
    cS
    ccrd
    cdm
    #
    wcel
    #
    cbs
    cvv
    wfn
    cgrp
    cvv
    wss
    @2
    @6
    wb
    basfn
    cgrp
    ssv
    vx
    cvv
    cgrp
    @1
    cbs
    fvelimab
    mp2an
    @5
    @8
    vx
    cgrp
    @3
    cgrp
    wcel
    #
    @5
    wa
    #
    @0
    @0
    cxp
    #
    @7
    wcel
    #
    cS
    @11
    cdom
    wbr
    #
    @8
    @0
    @7
    wcel
    #
    @14
    @12
    @0
    con0
    wcel
    @14
    cS
    harcl
    @0
    onenon
    ax-mp
    #
    @15
    @0
    @0
    xpnum
    mp2an
    #
    @10
    cS
    @11
    cwdom
    wbr
    #
    @13
    @10
    cS
    @0
    cS
    @0
    @3
    cplusg
    cfv
    #
    cvv
    @7
    @7
    va
    vc
    vd
    vb
    @10
    cS
    @4
    wss
    #
    cS
    cvv
    wcel
    @10
    @1
    cS
    @4
    cS
    @0
    ssun1
    @9
    @5
    simpr
    #
    syl5sseqr
    #
    cS
    @4
    @3
    cbs
    fvex
    ssex
    syl
    @14
    @10
    @15
    a1i
    #
    @22
    @10
    va
    cv
    #
    cS
    wcel
    #
    vc
    cv
    #
    @0
    wcel
    #
    w3a
    #
    @23
    @25
    @18
    co
    #
    @4
    @1
    @27
    @9
    @23
    @4
    wcel
    #
    @25
    @4
    wcel
    #
    @28
    @4
    wcel
    @9
    @5
    @24
    @26
    simp1l
    @27
    cS
    @4
    @23
    @10
    @24
    @19
    @26
    @21
    3ad2ant1
    @10
    @24
    @26
    simp2
    sseldd
    @27
    @0
    @4
    @25
    @10
    @24
    @0
    @4
    wss
    #
    @26
    @10
    @1
    @0
    @4
    @0
    cS
    ssun2
    @20
    syl5sseqr
    #
    3ad2ant1
    @10
    @24
    @26
    simp3
    sseldd
    @4
    @18
    @3
    @23
    @25
    @4
    eqid
    #
    @18
    eqid
    #
    grpcl
    syl3anc
    @9
    @5
    @24
    @26
    simp1r
    eleqtrd
    @10
    @24
    wa
    #
    @26
    vd
    cv
    #
    @0
    wcel
    #
    wa
    #
    wa
    #
    @9
    @30
    @36
    @4
    wcel
    #
    @29
    @28
    @23
    @36
    @18
    co
    wceq
    @25
    @36
    wceq
    wb
    @9
    @5
    @24
    @38
    simplll
    @39
    @0
    @4
    @25
    @10
    @31
    @24
    @38
    @32
    ad2antrr
    #
    @35
    @26
    @37
    simprl
    sseldd
    @39
    @0
    @4
    @36
    @41
    @35
    @26
    @37
    simprr
    sseldd
    @39
    cS
    @4
    @23
    @10
    @19
    @24
    @38
    @21
    ad2antrr
    @10
    @24
    @38
    simplr
    sseldd
    @4
    @18
    @3
    @25
    @36
    @23
    @33
    @34
    grplcan
    syl13anc
    @10
    vb
    cv
    #
    @0
    wcel
    #
    wa
    #
    @24
    @36
    cS
    wcel
    #
    wa
    #
    wa
    #
    @9
    @40
    @29
    @42
    @4
    wcel
    @36
    @42
    @18
    co
    @23
    @42
    @18
    co
    wceq
    @36
    @23
    wceq
    wb
    @9
    @5
    @43
    @46
    simplll
    @47
    cS
    @4
    @36
    @10
    @19
    @43
    @46
    @21
    ad2antrr
    #
    @44
    @24
    @45
    simprr
    sseldd
    @47
    cS
    @4
    @23
    @48
    @44
    @24
    @45
    simprl
    sseldd
    @47
    @0
    @4
    @42
    @10
    @31
    @43
    @46
    @32
    ad2antrr
    @10
    @43
    @46
    simplr
    sseldd
    @4
    @18
    @3
    @36
    @23
    @42
    @33
    @34
    grprcan
    syl13anc
    @0
    cS
    cdom
    wbr
    wn
    @10
    cS
    harndom
    a1i
    unxpwdom3
    @12
    @17
    @13
    wb
    @16
    cS
    @11
    wdomnumr
    ax-mp
    sylib
    @11
    cS
    numdom
    sylancr
    rexlimiva
    sylbi
end
