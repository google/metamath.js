include "ccnv.mm"
include "wss.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cxp.mm"
include "cin.mm"
include "cres.mm"
include "wceq.mm"
include "rnss.mm"
include "rncnv.mm"
include "sseq1i.mm"
include "biimpi.mm"
include "idreseqidinxp.mm"
include "3syl.mm"
include "sseq1d.mm"

theorem symrefref2
  let cR: class R


  assert |- ( `' R C_ R -> ( ( _I i^i ( dom R X. ran R ) ) C_ R <-> ( _I |` dom R ) C_ R ) )

  proof
    cR
    ccnv
    #
    cR
    wss
    #
    cid
    cR
    cdm
    #
    cR
    crn
    #
    cxp
    cin
    #
    cid
    @2
    cres
    #
    cR
    @1
    @0
    crn
    #
    @3
    wss
    #
    @2
    @3
    wss
    #
    @4
    @5
    wceq
    @0
    cR
    rnss
    @7
    @8
    @6
    @2
    @3
    cR
    rncnv
    sseq1i
    biimpi
    @2
    @3
    idreseqidinxp
    3syl
    sseq1d
end
