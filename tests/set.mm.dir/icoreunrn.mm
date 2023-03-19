include "cr.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cop.mm"
include "cico.mm"
include "cxp.mm"
include "cres.mm"
include "cfv.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "rexr.mm"
include "peano2re.mm"
include "syl.mm"
include "ltp1.mm"
include "lbico1.mm"
include "syl3anc.mm"
include "df-ov.mm"
include "syl6eleq.mm"
include "wceq.mm"
include "opelxpi.mm"
include "mpdan.mm"
include "fvres.mm"
include "eleqtrrd.mm"
include "cdm.mm"
include "wa.mm"
include "cpw.mm"
include "icoreresf.mm"
include "fdmi.mm"
include "syl6eleqr.mm"
include "crn.mm"
include "wfun.mm"
include "wf.mm"
include "ffun.mm"
include "ax-mp.mm"
include "fvelrn.mm"
include "mpan.mm"
include "cima.mm"
include "df-ima.mm"
include "eqtri.mm"
include "elunii.mm"
include "syl2anc.mm"
include "ssriv.mm"
include "wss.mm"
include "frn.mm"
include "eqsstri.mm"
include "uniss.mm"
include "unipw.mm"
include "syl6sseq.mm"
include "eqssi.mm"

theorem icoreunrn
  let cI: class I
  let vx: setvar x
  assume icoreunrn.1: |- I = ( [,) " ( RR X. RR ) )


  assert |- RR = U. I

  proof
    cr
    cI
    cuni
    #
    vx
    cr
    @0
    vx
    cv
    #
    cr
    wcel
    #
    @1
    @1
    @1
    c1
    caddc
    co
    #
    cop
    #
    cico
    cr
    cr
    cxp
    #
    cres
    #
    cfv
    #
    wcel
    @7
    cI
    wcel
    #
    @1
    @0
    wcel
    @2
    @1
    @4
    cico
    cfv
    #
    @7
    @2
    @1
    @1
    @3
    cico
    co
    #
    @9
    @2
    @1
    cxr
    wcel
    @3
    cxr
    wcel
    #
    @1
    @3
    clt
    wbr
    @1
    @10
    wcel
    @1
    rexr
    @2
    @3
    cr
    wcel
    #
    @11
    @1
    peano2re
    #
    @3
    rexr
    syl
    @1
    ltp1
    @1
    @3
    lbico1
    syl3anc
    @1
    @3
    cico
    df-ov
    syl6eleq
    @2
    @4
    @5
    wcel
    #
    @7
    @9
    wceq
    @2
    @12
    @14
    @13
    @1
    @3
    cr
    cr
    opelxpi
    #
    mpdan
    @4
    @5
    cico
    fvres
    syl
    eleqtrrd
    @2
    @4
    @6
    cdm
    #
    wcel
    #
    @8
    @2
    @12
    @17
    @13
    @2
    @12
    wa
    @4
    @5
    @16
    @15
    @5
    cr
    cpw
    #
    @6
    icoreresf
    fdmi
    syl6eleqr
    mpdan
    @17
    @7
    @6
    crn
    #
    cI
    @6
    wfun
    #
    @17
    @7
    @19
    wcel
    @5
    @18
    @6
    wf
    #
    @20
    icoreresf
    @5
    @18
    @6
    ffun
    ax-mp
    @4
    @6
    fvelrn
    mpan
    cI
    cico
    @5
    cima
    @19
    icoreunrn.1
    cico
    @5
    df-ima
    eqtri
    #
    syl6eleqr
    syl
    @1
    @7
    cI
    elunii
    syl2anc
    ssriv
    cI
    @18
    wss
    #
    @0
    cr
    wss
    cI
    @19
    @18
    @22
    @21
    @19
    @18
    wss
    icoreresf
    @5
    @18
    @6
    frn
    ax-mp
    eqsstri
    @23
    @0
    @18
    cuni
    cr
    cI
    @18
    uniss
    cr
    unipw
    syl6sseq
    ax-mp
    eqssi
end
