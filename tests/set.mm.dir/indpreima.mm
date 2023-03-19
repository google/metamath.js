include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "wf.mm"
include "wa.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cind.mm"
include "cfv.mm"
include "wfn.mm"
include "ffn.mm"
include "adantl.mm"
include "wss.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wceq.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "indf.mm"
include "syldan.mm"
include "syl.mm"
include "cv.mm"
include "simpr.mm"
include "ffvelrnda.mm"
include "prcom.mm"
include "syl6eleq.mm"
include "wb.mm"
include "simpll.mm"
include "adantr.mm"
include "ind1a.mm"
include "syl3anc.mm"
include "fniniseg.mm"
include "baibd.mm"
include "bitr2d.mm"
include "elpreq.mm"
include "eqfnfvd.mm"

theorem indpreima
  let cF: class F
  let cO: class O
  let cV: class V
  let vx: setvar x


  assert |- ( ( O e. V /\ F : O --> { 0 , 1 } ) -> F = ( ( _Ind ` O ) ` ( `' F " { 1 } ) ) )

  proof
    cO
    cV
    wcel
    #
    cO
    cc0
    c1
    cpr
    #
    cF
    wf
    #
    wa
    #
    vx
    cO
    cF
    cF
    ccnv
    c1
    csn
    #
    cima
    #
    cO
    cind
    cfv
    cfv
    #
    @2
    cF
    cO
    wfn
    #
    @0
    cO
    @1
    cF
    ffn
    adantl
    #
    @3
    cO
    @1
    @6
    wf
    #
    @6
    cO
    wfn
    @0
    @2
    @5
    cO
    wss
    #
    @9
    @3
    cF
    cdm
    #
    @5
    cO
    cF
    @4
    cnvimass
    @2
    @11
    cO
    wceq
    @0
    cO
    @1
    cF
    fdm
    adantl
    syl5sseq
    #
    @5
    cO
    cV
    indf
    syldan
    #
    cO
    @1
    @6
    ffn
    syl
    @3
    vx
    cv
    #
    cO
    wcel
    #
    wa
    #
    c1
    cc0
    @14
    cF
    cfv
    #
    @14
    @6
    cfv
    #
    @16
    @17
    @1
    c1
    cc0
    cpr
    #
    @3
    cO
    @1
    @14
    cF
    @0
    @2
    simpr
    ffvelrnda
    cc0
    c1
    prcom
    #
    syl6eleq
    @16
    @18
    @1
    @19
    @3
    cO
    @1
    @14
    @6
    @13
    ffvelrnda
    @20
    syl6eleq
    @16
    @18
    c1
    wceq
    #
    @14
    @5
    wcel
    #
    @17
    c1
    wceq
    #
    @16
    @0
    @10
    @15
    @21
    @22
    wb
    @0
    @2
    @15
    simpll
    @3
    @10
    @15
    @12
    adantr
    @3
    @15
    simpr
    @5
    cO
    cV
    @14
    ind1a
    syl3anc
    @3
    @22
    @15
    @23
    @3
    @7
    @22
    @15
    @23
    wa
    wb
    @8
    cO
    c1
    @14
    cF
    fniniseg
    syl
    baibd
    bitr2d
    elpreq
    eqfnfvd
end
