include "cr.mm"
include "ccos.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "cc.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "csin.mm"
include "cneg.mm"
include "cpr.mm"
include "wcel.mm"
include "wf.mm"
include "wss.mm"
include "cdm.mm"
include "wceq.mm"
include "reelprrecn.mm"
include "cosf.mm"
include "ssid.mm"
include "cvv.mm"
include "crab.mm"
include "wi.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "dfss2f.mm"
include "recn.mm"
include "sincld.mm"
include "negcld.mm"
include "elex.mm"
include "syl.mm"
include "rabid.mm"
include "sylanbrc.mm"
include "mpgbir.mm"
include "dvcos.mm"
include "dmmpt.mm"
include "sseqtr4i.mm"
include "dvres3.mm"
include "mp4an.mm"
include "wfn.mm"
include "ffn.mm"
include "ax-mp.mm"
include "dffn5.mm"
include "mpbi.mm"
include "reseq1i.mm"
include "ax-resscn.mm"
include "resmpt.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "3eqtr3i.mm"

theorem dvcosre
  let vx: setvar x
  let vk: setvar k


  assert |- ( RR _D ( x e. RR |-> ( cos ` x ) ) ) = ( x e. RR |-> -u ( sin ` x ) )

  proof
    cr
    ccos
    cr
    cres
    #
    cdv
    co
    #
    cc
    ccos
    cdv
    co
    #
    cr
    cres
    #
    cr
    vx
    cr
    vx
    cv
    #
    ccos
    cfv
    #
    cmpt
    #
    cdv
    co
    vx
    cr
    @4
    csin
    cfv
    #
    cneg
    #
    cmpt
    #
    cr
    cr
    cc
    cpr
    wcel
    cc
    cc
    ccos
    wf
    #
    cc
    cc
    wss
    cr
    @2
    cdm
    #
    wss
    @1
    @3
    wceq
    reelprrecn
    cosf
    cc
    ssid
    cr
    @8
    cvv
    wcel
    #
    vx
    cc
    crab
    #
    @11
    cr
    @13
    wss
    @4
    cr
    wcel
    #
    @4
    @13
    wcel
    #
    wi
    vx
    vx
    cr
    @13
    vx
    cr
    nfcv
    @12
    vx
    cc
    nfrab1
    dfss2f
    @14
    @4
    cc
    wcel
    @12
    @15
    @4
    recn
    #
    @14
    @8
    cc
    wcel
    @12
    @14
    @7
    @14
    @4
    @16
    sincld
    negcld
    @8
    cc
    elex
    syl
    @12
    vx
    cc
    rabid
    sylanbrc
    mpgbir
    vx
    cc
    @8
    @2
    vx
    dvcos
    #
    dmmpt
    sseqtr4i
    cc
    cr
    ccos
    dvres3
    mp4an
    @0
    @6
    cr
    cdv
    @0
    vx
    cc
    @5
    cmpt
    #
    cr
    cres
    #
    @6
    ccos
    @18
    cr
    ccos
    cc
    wfn
    #
    ccos
    @18
    wceq
    @10
    @20
    cosf
    cc
    cc
    ccos
    ffn
    ax-mp
    vx
    cc
    ccos
    dffn5
    mpbi
    reseq1i
    cr
    cc
    wss
    #
    @19
    @6
    wceq
    ax-resscn
    vx
    cc
    cr
    @5
    resmpt
    ax-mp
    eqtri
    oveq2i
    @3
    vx
    cc
    @8
    cmpt
    #
    cr
    cres
    #
    @9
    @2
    @22
    cr
    @17
    reseq1i
    @21
    @23
    @9
    wceq
    ax-resscn
    vx
    cc
    cr
    @8
    resmpt
    ax-mp
    eqtri
    3eqtr3i
end
