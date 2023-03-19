include "ccnv.mm"
include "wfun.mm"
include "cima.mm"
include "cres.mm"
include "cdm.mm"
include "crn.mm"
include "df-ima.mm"
include "df-rn.mm"
include "eqtri.mm"
include "reseq2i.mm"
include "wss.mm"
include "wceq.mm"
include "resss.mm"
include "cnvss.mm"
include "ax-mp.mm"
include "funssres.mm"
include "mpan2.mm"
include "syl5req.mm"

theorem funcnvres
  let cA: class A
  let cF: class F


  assert |- ( Fun `' F -> `' ( F |` A ) = ( `' F |` ( F " A ) ) )

  proof
    cF
    ccnv
    #
    wfun
    #
    @0
    cF
    cA
    cima
    #
    cres
    @0
    cF
    cA
    cres
    #
    ccnv
    #
    cdm
    #
    cres
    #
    @4
    @2
    @5
    @0
    @2
    @3
    crn
    @5
    cF
    cA
    df-ima
    @3
    df-rn
    eqtri
    reseq2i
    @1
    @4
    @0
    wss
    #
    @6
    @4
    wceq
    @3
    cF
    wss
    @7
    cF
    cA
    resss
    @3
    cF
    cnvss
    ax-mp
    @0
    @4
    funssres
    mpan2
    syl5req
end
