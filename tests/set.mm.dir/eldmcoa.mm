include "cdm.mm"
include "wbr.mm"
include "cop.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "ccoda.mm"
include "cfv.mm"
include "cdoma.mm"
include "wceq.mm"
include "crab.mm"
include "cxp.mm"
include "ciun.mm"
include "w3a.mm"
include "df-br.mm"
include "cvv.mm"
include "c2nd.mm"
include "cco.mm"
include "co.mm"
include "cotp.mm"
include "wral.mm"
include "wf.mm"
include "otex.mm"
include "rgen2w.mm"
include "eqid.mm"
include "coafval.mm"
include "fmpt2x.mm"
include "mpbi.mm"
include "fdmi.mm"
include "eleq2i.mm"
include "wa.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "rabbidv.mm"
include "opeliunxp2.mm"
include "eqeq1d.mm"
include "elrab.mm"
include "anbi2i.mm"
include "an12.mm"
include "3anass.mm"
include "bitr4i.mm"
include "3bitri.mm"

theorem eldmcoa
  let cA: class A
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let c.xb: class .xb
  assume coafval.o: |- .x. = ( compA ` C )
  assume coafval.a: |- A = ( Arrow ` C )


  assert |- ( G dom .x. F <-> ( F e. A /\ G e. A /\ ( codA ` F ) = ( domA ` G ) ) )

  proof
    cG
    cF
    c.x
    cdm
    #
    wbr
    cG
    cF
    cop
    #
    @0
    wcel
    @1
    vg
    cA
    vg
    cv
    #
    csn
    vh
    cv
    #
    ccoda
    cfv
    #
    @2
    cdoma
    cfv
    #
    wceq
    #
    vh
    cA
    crab
    #
    cxp
    ciun
    #
    wcel
    #
    cF
    cA
    wcel
    #
    cG
    cA
    wcel
    #
    cF
    ccoda
    cfv
    #
    cG
    cdoma
    cfv
    #
    wceq
    #
    w3a
    #
    cG
    cF
    @0
    df-br
    @0
    @8
    @1
    @8
    cvv
    c.x
    vf
    cv
    #
    cdoma
    cfv
    #
    @2
    ccoda
    cfv
    #
    @2
    c2nd
    cfv
    @16
    c2nd
    cfv
    @17
    @5
    cop
    @18
    cC
    cco
    cfv
    #
    co
    co
    #
    cotp
    #
    cvv
    wcel
    #
    vf
    @7
    wral
    vg
    cA
    wral
    @8
    cvv
    c.x
    wf
    @22
    vg
    vf
    cA
    @7
    @17
    @18
    @20
    otex
    rgen2w
    vg
    vf
    cA
    @7
    @21
    cvv
    c.x
    cA
    cC
    @19
    c.x
    vf
    vg
    vh
    coafval.o
    coafval.a
    @19
    eqid
    coafval
    fmpt2x
    mpbi
    fdmi
    eleq2i
    @9
    @11
    cF
    @4
    @13
    wceq
    #
    vh
    cA
    crab
    #
    wcel
    #
    wa
    @11
    @10
    @14
    wa
    #
    wa
    #
    @15
    vg
    cA
    @7
    cG
    cF
    @24
    @2
    cG
    wceq
    #
    @6
    @23
    vh
    cA
    @28
    @5
    @13
    @4
    @2
    cG
    cdoma
    fveq2
    eqeq2d
    rabbidv
    opeliunxp2
    @25
    @26
    @11
    @23
    @14
    vh
    cF
    cA
    @3
    cF
    wceq
    @4
    @12
    @13
    @3
    cF
    ccoda
    fveq2
    eqeq1d
    elrab
    anbi2i
    @27
    @10
    @11
    @14
    wa
    wa
    @15
    @11
    @10
    @14
    an12
    @10
    @11
    @14
    3anass
    bitr4i
    3bitri
    3bitri
end
