include "wfo.mm"
include "wss.mm"
include "wa.mm"
include "ccnv.mm"
include "cima.mm"
include "cres.mm"
include "resima.mm"
include "wfun.mm"
include "wceq.mm"
include "fofun.mm"
include "adantr.mm"
include "funcnvres2.mm"
include "syl.mm"
include "imaeq1d.mm"
include "wfn.mm"
include "crn.mm"
include "cdm.mm"
include "resss.mm"
include "cnvss.mm"
include "ax-mp.mm"
include "cnvcnvss.mm"
include "sstri.mm"
include "funss.mm"
include "mpsyl.mm"
include "df-ima.mm"
include "df-rn.mm"
include "eqtr2i.mm"
include "jctir.mm"
include "df-fn.mm"
include "sylibr.mm"
include "dfdm4.mm"
include "forn.mm"
include "sseq2d.mm"
include "biimpar.mm"
include "syl6sseq.mm"
include "ssdmres.mm"
include "sylib.mm"
include "syl5eqr.mm"
include "df-fo.mm"
include "sylanbrc.mm"
include "foima.mm"
include "eqtr3d.mm"

theorem foimacnv
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( ( F : A -onto-> B /\ C C_ B ) -> ( F " ( `' F " C ) ) = C )

  proof
    cA
    cB
    cF
    wfo
    #
    cC
    cB
    wss
    #
    wa
    #
    cF
    cF
    ccnv
    #
    cC
    cima
    #
    cima
    cF
    @4
    cres
    #
    @4
    cima
    #
    cC
    cF
    @4
    resima
    @2
    @3
    cC
    cres
    #
    ccnv
    #
    @4
    cima
    #
    @6
    cC
    @2
    @8
    @5
    @4
    @2
    cF
    wfun
    #
    @8
    @5
    wceq
    @0
    @10
    @1
    cA
    cB
    cF
    fofun
    #
    adantr
    cC
    cF
    funcnvres2
    syl
    imaeq1d
    @2
    @4
    cC
    @8
    wfo
    #
    @9
    cC
    wceq
    @2
    @8
    @4
    wfn
    #
    @8
    crn
    #
    cC
    wceq
    @12
    @2
    @8
    wfun
    #
    @8
    cdm
    #
    @4
    wceq
    #
    wa
    @13
    @2
    @15
    @17
    @0
    @15
    @1
    @8
    cF
    wss
    @0
    @10
    @15
    @8
    @3
    ccnv
    #
    cF
    @7
    @3
    wss
    @8
    @18
    wss
    @3
    cC
    resss
    @7
    @3
    cnvss
    ax-mp
    cF
    cnvcnvss
    sstri
    @11
    @8
    cF
    funss
    mpsyl
    adantr
    @4
    @7
    crn
    @16
    @3
    cC
    df-ima
    @7
    df-rn
    eqtr2i
    jctir
    @8
    @4
    df-fn
    sylibr
    @2
    @14
    @7
    cdm
    #
    cC
    @7
    dfdm4
    @2
    cC
    @3
    cdm
    #
    wss
    @19
    cC
    wceq
    @2
    cC
    cF
    crn
    #
    @20
    @0
    cC
    @21
    wss
    @1
    @0
    @21
    cB
    cC
    cA
    cB
    cF
    forn
    sseq2d
    biimpar
    cF
    df-rn
    syl6sseq
    cC
    @3
    ssdmres
    sylib
    syl5eqr
    @4
    cC
    @8
    df-fo
    sylanbrc
    @4
    cC
    @8
    foima
    syl
    eqtr3d
    syl5eqr
end
