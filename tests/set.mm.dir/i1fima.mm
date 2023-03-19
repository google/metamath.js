include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "crn.mm"
include "cin.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "ciun.mm"
include "cvol.mm"
include "cr.mm"
include "wf.mm"
include "wfun.mm"
include "wceq.mm"
include "i1ff.mm"
include "ffun.mm"
include "inpreima.mm"
include "iunid.mm"
include "imaeq2i.mm"
include "imaiun.mm"
include "eqtr3i.mm"
include "wss.mm"
include "cnvimass.mm"
include "cnvimarndm.mm"
include "sseqtr4i.mm"
include "df-ss.mm"
include "mpbi.mm"
include "3eqtr3g.mm"
include "3syl.mm"
include "cfn.mm"
include "wral.mm"
include "i1frn.mm"
include "inss2.mm"
include "ssfi.mm"
include "sylancl.mm"
include "wa.mm"
include "cmbf.mm"
include "i1fmbf.mm"
include "adantr.mm"
include "frn.mm"
include "syl.mm"
include "syl5ss.mm"
include "sselda.mm"
include "mbfimasn.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "finiunmbl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem i1fima
  let cA: class A
  let cF: class F
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y


  assert |- ( F e. dom S.1 -> ( `' F " A ) e. dom vol )

  proof
    cF
    citg1
    cdm
    wcel
    #
    vy
    cA
    cF
    crn
    #
    cin
    #
    cF
    ccnv
    #
    vy
    cv
    #
    csn
    #
    cima
    #
    ciun
    #
    @3
    cA
    cima
    #
    cvol
    cdm
    #
    @0
    cr
    cr
    cF
    wf
    #
    cF
    wfun
    #
    @7
    @8
    wceq
    cF
    i1ff
    #
    cr
    cr
    cF
    ffun
    @11
    @3
    @2
    cima
    #
    @8
    @3
    @1
    cima
    #
    cin
    #
    @7
    @8
    cA
    @1
    cF
    inpreima
    @3
    vy
    @2
    @5
    ciun
    #
    cima
    @13
    @7
    @16
    @2
    @3
    vy
    @2
    iunid
    imaeq2i
    vy
    @3
    @2
    @5
    imaiun
    eqtr3i
    @8
    @14
    wss
    @15
    @8
    wceq
    @8
    cF
    cdm
    @14
    cF
    cA
    cnvimass
    cF
    cnvimarndm
    sseqtr4i
    @8
    @14
    df-ss
    mpbi
    3eqtr3g
    3syl
    @0
    @2
    cfn
    wcel
    #
    @6
    @9
    wcel
    #
    vy
    @2
    wral
    @7
    @9
    wcel
    @0
    @1
    cfn
    wcel
    @2
    @1
    wss
    @17
    cF
    i1frn
    cA
    @1
    inss2
    #
    @1
    @2
    ssfi
    sylancl
    @0
    @18
    vy
    @2
    @0
    @4
    @2
    wcel
    #
    wa
    cF
    cmbf
    wcel
    #
    @10
    @4
    cr
    wcel
    @18
    @0
    @21
    @20
    cF
    i1fmbf
    adantr
    @0
    @10
    @20
    @12
    adantr
    @0
    @2
    cr
    @4
    @0
    @2
    @1
    cr
    @19
    @0
    @10
    @1
    cr
    wss
    @12
    cr
    cr
    cF
    frn
    syl
    syl5ss
    sselda
    cr
    @4
    cF
    mbfimasn
    syl3anc
    ralrimiva
    @2
    @6
    vy
    finiunmbl
    syl2anc
    eqeltrrd
end
