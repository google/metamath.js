include "wfn.mm"
include "ccnv.mm"
include "ccom.mm"
include "wrel.mm"
include "cdm.mm"
include "wceq.mm"
include "cun.mm"
include "wss.mm"
include "wer.mm"
include "relco.mm"
include "a1i.mm"
include "cima.mm"
include "dmco.mm"
include "crn.mm"
include "df-rn.mm"
include "imaeq2i.mm"
include "cnvimarndm.mm"
include "fndm.mm"
include "syl5eq.mm"
include "syl5eqr.mm"
include "cnvco.mm"
include "cnvcnvss.mm"
include "coss2.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "wfun.mm"
include "fnfun.mm"
include "funcocnv2.mm"
include "syl.mm"
include "coeq1d.mm"
include "wf.mm"
include "dffn3.mm"
include "fcoi2.mm"
include "sylbi.mm"
include "eqtrd.mm"
include "coeq2d.mm"
include "ssid.mm"
include "syl6eqss.mm"
include "unssd.mm"
include "df-er.mm"
include "syl3anbrc.mm"

theorem fcoinver
  let cF: class F
  let cX: class X


  assert |- ( F Fn X -> ( `' F o. F ) Er X )

  proof
    cF
    cX
    wfn
    #
    cF
    ccnv
    #
    cF
    ccom
    #
    wrel
    #
    @2
    cdm
    #
    cX
    wceq
    @2
    ccnv
    #
    @2
    @2
    ccom
    #
    cun
    @2
    wss
    cX
    @2
    wer
    @3
    @0
    @1
    cF
    relco
    a1i
    @0
    @4
    @1
    @1
    cdm
    #
    cima
    #
    cX
    @1
    cF
    dmco
    @0
    @8
    @1
    cF
    crn
    #
    cima
    #
    cX
    @9
    @7
    @1
    cF
    df-rn
    imaeq2i
    @0
    @10
    cF
    cdm
    cX
    cF
    cnvimarndm
    cX
    cF
    fndm
    syl5eq
    syl5eqr
    syl5eq
    @0
    @5
    @6
    @2
    @5
    @2
    wss
    @0
    @5
    @1
    @1
    ccnv
    #
    ccom
    #
    @2
    @1
    cF
    cnvco
    @11
    cF
    wss
    @12
    @2
    wss
    cF
    cnvcnvss
    @11
    cF
    @1
    coss2
    ax-mp
    eqsstri
    a1i
    @0
    @6
    @2
    @2
    @0
    @6
    @1
    cF
    @2
    ccom
    #
    ccom
    @2
    @1
    cF
    @2
    coass
    @0
    @13
    cF
    @1
    @0
    @13
    cF
    @1
    ccom
    #
    cF
    ccom
    #
    cF
    cF
    @1
    cF
    coass
    @0
    @15
    cid
    @9
    cres
    #
    cF
    ccom
    #
    cF
    @0
    @14
    @16
    cF
    @0
    cF
    wfun
    @14
    @16
    wceq
    cX
    cF
    fnfun
    cF
    funcocnv2
    syl
    coeq1d
    @0
    cX
    @9
    cF
    wf
    @17
    cF
    wceq
    cX
    cF
    dffn3
    cX
    @9
    cF
    fcoi2
    sylbi
    eqtrd
    syl5eqr
    coeq2d
    syl5eq
    @2
    ssid
    syl6eqss
    unssd
    cX
    @2
    df-er
    syl3anbrc
end
