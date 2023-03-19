include "cxp.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cdm.mm"
include "wf.mm"
include "wss.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wfun.mm"
include "ccoda.mm"
include "cdoma.mm"
include "wceq.mm"
include "crab.mm"
include "c2nd.mm"
include "cop.mm"
include "cco.mm"
include "cotp.mm"
include "eqid.mm"
include "coafval.mm"
include "mpt2fun.mm"
include "funfn.mm"
include "mpbi.mm"
include "c1st.mm"
include "dmcoass.mm"
include "sseli.mm"
include "1st2nd2.mm"
include "syl.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "choma.mm"
include "homarw.mm"
include "wbr.mm"
include "w3a.mm"
include "id.mm"
include "eqeltrrd.mm"
include "df-br.mm"
include "sylibr.mm"
include "eldmcoa.mm"
include "sylib.mm"
include "simp1d.mm"
include "arwhoma.mm"
include "simp3d.mm"
include "oveq2d.mm"
include "eleqtrd.mm"
include "simp2d.mm"
include "coahom.mm"
include "sseldi.mm"
include "eqeltrd.mm"
include "rgen.mm"
include "ffnfv.mm"
include "mpbir2an.mm"
include "carw.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "elpm2.mm"

theorem coapm
  let cA: class A
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vz: setvar z
  assume coapm.o: |- .x. = ( compA ` C )
  assume coapm.a: |- A = ( Arrow ` C )


  assert |- .x. e. ( A ^pm ( A X. A ) )

  proof
    c.x
    cA
    cA
    cA
    cxp
    #
    cpm
    co
    wcel
    c.x
    cdm
    #
    cA
    c.x
    wf
    #
    @1
    @0
    wss
    @2
    c.x
    @1
    wfn
    #
    vz
    cv
    #
    c.x
    cfv
    #
    cA
    wcel
    #
    vz
    @1
    wral
    c.x
    wfun
    @3
    vg
    vf
    cA
    vh
    cv
    ccoda
    cfv
    vg
    cv
    #
    cdoma
    cfv
    #
    wceq
    vh
    cA
    crab
    vf
    cv
    #
    cdoma
    cfv
    #
    @7
    ccoda
    cfv
    #
    @7
    c2nd
    cfv
    @9
    c2nd
    cfv
    @10
    @8
    cop
    @11
    cC
    cco
    cfv
    #
    co
    co
    cotp
    c.x
    cA
    cC
    @12
    c.x
    vf
    vg
    vh
    coapm.o
    coapm.a
    @12
    eqid
    coafval
    mpt2fun
    c.x
    funfn
    mpbi
    @6
    vz
    @1
    @4
    @1
    wcel
    #
    @5
    @4
    c1st
    cfv
    #
    @4
    c2nd
    cfv
    #
    c.x
    co
    #
    cA
    @13
    @5
    @14
    @15
    cop
    #
    c.x
    cfv
    @16
    @13
    @4
    @17
    c.x
    @13
    @4
    @0
    wcel
    @4
    @17
    wceq
    @1
    @0
    @4
    cA
    cC
    c.x
    coapm.o
    coapm.a
    dmcoass
    #
    sseli
    @4
    cA
    cA
    1st2nd2
    syl
    #
    fveq2d
    @14
    @15
    c.x
    df-ov
    syl6eqr
    @13
    @15
    cdoma
    cfv
    #
    @14
    ccoda
    cfv
    #
    cC
    choma
    cfv
    #
    co
    cA
    @16
    cA
    cC
    @22
    @20
    @21
    coapm.a
    @22
    eqid
    #
    homarw
    @13
    cC
    c.x
    @15
    @14
    @22
    @20
    @14
    cdoma
    cfv
    #
    @21
    coapm.o
    @23
    @13
    @15
    @20
    @15
    ccoda
    cfv
    #
    @22
    co
    #
    @20
    @24
    @22
    co
    @13
    @15
    cA
    wcel
    #
    @15
    @26
    wcel
    @13
    @27
    @14
    cA
    wcel
    #
    @25
    @24
    wceq
    #
    @13
    @14
    @15
    @1
    wbr
    #
    @27
    @28
    @29
    w3a
    @13
    @17
    @1
    wcel
    @30
    @13
    @4
    @17
    @1
    @19
    @13
    id
    eqeltrrd
    @14
    @15
    @1
    df-br
    sylibr
    cA
    cC
    c.x
    @15
    @14
    coapm.o
    coapm.a
    eldmcoa
    sylib
    #
    simp1d
    cA
    cC
    @15
    @22
    coapm.a
    @23
    arwhoma
    syl
    @13
    @25
    @24
    @20
    @22
    @13
    @27
    @28
    @29
    @31
    simp3d
    oveq2d
    eleqtrd
    @13
    @28
    @14
    @24
    @21
    @22
    co
    wcel
    @13
    @27
    @28
    @29
    @31
    simp2d
    cA
    cC
    @14
    @22
    coapm.a
    @23
    arwhoma
    syl
    coahom
    sseldi
    eqeltrd
    rgen
    vz
    @1
    cA
    c.x
    ffnfv
    mpbir2an
    @18
    cA
    @0
    c.x
    cA
    cC
    carw
    cfv
    cvv
    coapm.a
    cC
    carw
    fvex
    eqeltri
    #
    cA
    cA
    @32
    @32
    xpex
    elpm2
    mpbir2an
end
