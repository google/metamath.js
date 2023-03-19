include "c0.mm"
include "clspn.mm"
include "cfv.mm"
include "cpw.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cint.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "0ex.mm"
include "base0.mm"
include "00lss.mm"
include "eqid.mm"
include "lspfval.mm"
include "ax-mp.mm"
include "cdm.mm"
include "dmmpt.mm"
include "wn.mm"
include "wral.mm"
include "vprc.mm"
include "rab0.mm"
include "inteqi.mm"
include "int0.mm"
include "eqtri.mm"
include "eleq1i.mm"
include "mtbir.mm"
include "rgenw.mm"
include "rabeq0.mm"
include "mpbir.mm"
include "wrel.mm"
include "wb.mm"
include "wfun.mm"
include "funmpt.mm"
include "funrel.mm"
include "reldm0.mm"
include "eqtr2i.mm"

theorem 00lsp
  let va: setvar a
  let vb: setvar b


  assert |- (/) = ( LSpan ` (/) )

  proof
    c0
    clspn
    cfv
    #
    va
    c0
    cpw
    #
    va
    cv
    vb
    cv
    wss
    #
    vb
    c0
    crab
    #
    cint
    #
    cmpt
    #
    c0
    c0
    cvv
    wcel
    @0
    @5
    wceq
    0ex
    vb
    c0
    @0
    c0
    c0
    cvv
    va
    base0
    00lss
    @0
    eqid
    lspfval
    ax-mp
    @5
    c0
    wceq
    #
    @5
    cdm
    #
    c0
    wceq
    #
    @7
    @4
    cvv
    wcel
    #
    va
    @1
    crab
    #
    c0
    va
    @1
    @4
    @5
    @5
    eqid
    dmmpt
    @10
    c0
    wceq
    @9
    wn
    #
    va
    @1
    wral
    @11
    va
    @1
    @9
    cvv
    cvv
    wcel
    vprc
    @4
    cvv
    cvv
    @4
    c0
    cint
    cvv
    @3
    c0
    @2
    vb
    rab0
    inteqi
    int0
    eqtri
    eleq1i
    mtbir
    rgenw
    @9
    va
    @1
    rabeq0
    mpbir
    eqtri
    @5
    wrel
    #
    @6
    @8
    wb
    @5
    wfun
    @12
    va
    @1
    @4
    funmpt
    @5
    funrel
    ax-mp
    @5
    reldm0
    ax-mp
    mpbir
    eqtr2i
end
