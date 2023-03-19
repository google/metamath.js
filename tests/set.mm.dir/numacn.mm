include "wcel.mm"
include "cvv.mm"
include "ccrd.mm"
include "cdm.mm"
include "wacn.mm"
include "wi.mm"
include "elex.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "wex.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cmap.mm"
include "co.mm"
include "crn.mm"
include "cuni.mm"
include "wf.mm"
include "wn.mm"
include "wss.mm"
include "simpll.mm"
include "elmapi.mm"
include "adantl.mm"
include "frn.mm"
include "syl.mm"
include "difss2d.mm"
include "sspwuni.mm"
include "sylib.mm"
include "ssnum.mm"
include "syl2anc.mm"
include "cin.mm"
include "wceq.mm"
include "ssdifin0.mm"
include "disjsn.mm"
include "ac5num.mm"
include "simpllr.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "fveq2.mm"
include "id.mm"
include "eleq12d.mm"
include "ralrn.mm"
include "biimpa.mm"
include "adantrl.mm"
include "acnlem.mm"
include "exlimddv.mm"
include "ralrimiva.mm"
include "isacn.mm"
include "mpbird.mm"
include "expcom.mm"

theorem numacn
  let cA: class A
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cF: class F
  let wph: wff ph
  let wps: wff ps
  let cC: class C


  assert |- ( A e. V -> ( X e. dom card -> X e. AC_ A ) )

  proof
    cA
    cV
    wcel
    cA
    cvv
    wcel
    #
    cX
    ccrd
    cdm
    #
    wcel
    #
    cX
    cA
    wacn
    wcel
    #
    wi
    cA
    cV
    elex
    @2
    @0
    @3
    @2
    @0
    wa
    #
    @3
    vx
    cv
    #
    vg
    cv
    cfv
    @5
    vf
    cv
    #
    cfv
    #
    wcel
    vx
    cA
    wral
    vg
    wex
    #
    vf
    cX
    cpw
    #
    c0
    csn
    #
    cdif
    #
    cA
    cmap
    co
    #
    wral
    @4
    @8
    vf
    @12
    @4
    @6
    @12
    wcel
    #
    wa
    #
    @6
    crn
    #
    @15
    cuni
    #
    vh
    cv
    #
    wf
    #
    vy
    cv
    #
    @17
    cfv
    #
    @19
    wcel
    #
    vy
    @15
    wral
    #
    wa
    #
    @8
    vh
    @14
    @16
    @1
    wcel
    #
    c0
    @15
    wcel
    wn
    #
    @23
    vh
    wex
    @14
    @2
    @16
    cX
    wss
    #
    @24
    @2
    @0
    @13
    simpll
    @14
    @15
    @9
    wss
    @26
    @14
    @15
    @9
    @10
    @14
    cA
    @11
    @6
    wf
    #
    @15
    @11
    wss
    #
    @13
    @27
    @4
    @6
    @11
    cA
    elmapi
    adantl
    #
    cA
    @11
    @6
    frn
    syl
    #
    difss2d
    @15
    cX
    sspwuni
    sylib
    cX
    @16
    ssnum
    syl2anc
    @14
    @15
    @10
    cin
    c0
    wceq
    #
    @25
    @14
    @28
    @31
    @30
    @15
    @9
    @10
    ssdifin0
    syl
    @15
    c0
    disjsn
    sylib
    vy
    @15
    vh
    ac5num
    syl2anc
    @14
    @23
    wa
    @0
    @7
    @17
    cfv
    #
    @7
    wcel
    #
    vx
    cA
    wral
    #
    @8
    @2
    @0
    @13
    @23
    simpllr
    @14
    @22
    @34
    @18
    @14
    @22
    @34
    @14
    @6
    cA
    wfn
    #
    @22
    @34
    wb
    @14
    @27
    @35
    @29
    cA
    @11
    @6
    ffn
    syl
    @21
    @33
    vy
    vx
    cA
    @6
    @19
    @7
    wceq
    #
    @20
    @32
    @19
    @7
    @19
    @7
    @17
    fveq2
    @36
    id
    eleq12d
    ralrn
    syl
    biimpa
    adantrl
    vx
    cA
    @32
    vf
    vg
    cvv
    acnlem
    syl2anc
    exlimddv
    ralrimiva
    vx
    cA
    vf
    vg
    @1
    cvv
    cX
    isacn
    mpbird
    expcom
    syl
end
