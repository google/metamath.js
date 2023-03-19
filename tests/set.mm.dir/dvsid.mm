include "cr.mm"
include "cc.mm"
include "cpr.mm"
include "wcel.mm"
include "cid.mm"
include "cres.mm"
include "cdv.mm"
include "co.mm"
include "c1.mm"
include "csn.mm"
include "cxp.mm"
include "wf.mm"
include "wa.mm"
include "wss.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "crn.mm"
include "fnresi.mm"
include "rnresi.mm"
include "eqimssi.mm"
include "df-f.mm"
include "mpbir2an.mm"
include "jctr.mm"
include "recnprss.mm"
include "dvid.mm"
include "dmeqi.mm"
include "1ex.mm"
include "fconst.mm"
include "fdmi.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "ssid.mm"
include "jctil.mm"
include "dvres3.mm"
include "syl2anc.mm"
include "resabs1d.mm"
include "oveq2d.mm"
include "reseq1i.mm"
include "xpssres.mm"
include "syl5eq.mm"
include "syl.mm"
include "3eqtr3d.mm"

theorem dvsid
  let cS: class S


  assert |- ( S e. { RR , CC } -> ( S _D ( _I |` S ) ) = ( S X. { 1 } ) )

  proof
    cS
    cr
    cc
    cpr
    wcel
    #
    cS
    cid
    cc
    cres
    #
    cS
    cres
    #
    cdv
    co
    #
    cc
    @1
    cdv
    co
    #
    cS
    cres
    #
    cS
    cid
    cS
    cres
    #
    cdv
    co
    cS
    c1
    csn
    #
    cxp
    #
    @0
    @0
    cc
    cc
    @1
    wf
    #
    wa
    cc
    cc
    wss
    #
    cS
    @4
    cdm
    #
    wss
    #
    wa
    @3
    @5
    wceq
    @0
    @9
    @9
    @1
    cc
    wfn
    @1
    crn
    #
    cc
    wss
    cc
    fnresi
    @13
    cc
    cc
    rnresi
    eqimssi
    cc
    cc
    @1
    df-f
    mpbir2an
    jctr
    @0
    @12
    @10
    @0
    cS
    cc
    @11
    cS
    recnprss
    #
    @11
    cc
    @7
    cxp
    #
    cdm
    cc
    @4
    @15
    dvid
    dmeqi
    cc
    @7
    @15
    cc
    c1
    1ex
    fconst
    fdmi
    eqtri
    syl6sseqr
    cc
    ssid
    jctil
    cc
    cS
    @1
    dvres3
    syl2anc
    @0
    @2
    @6
    cS
    cdv
    @0
    cid
    cS
    cc
    @14
    resabs1d
    oveq2d
    @0
    cS
    cc
    wss
    #
    @5
    @8
    wceq
    @14
    @16
    @5
    @15
    cS
    cres
    @8
    @4
    @15
    cS
    dvid
    reseq1i
    cc
    @7
    cS
    xpssres
    syl5eq
    syl
    3eqtr3d
end
