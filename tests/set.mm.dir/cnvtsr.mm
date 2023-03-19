include "ctsr.mm"
include "wcel.mm"
include "ccnv.mm"
include "cps.mm"
include "crn.mm"
include "cxp.mm"
include "cun.mm"
include "wss.mm"
include "tsrps.mm"
include "cnvps.mm"
include "syl.mm"
include "cdm.mm"
include "eqid.mm"
include "istsr.mm"
include "simprbi.mm"
include "wceq.mm"
include "psrn.mm"
include "sqxpeqd.mm"
include "wrel.mm"
include "psrel.mm"
include "dfrel2.mm"
include "sylib.mm"
include "uneq2d.mm"
include "uncom.mm"
include "syl6req.mm"
include "3sstr3d.mm"
include "df-rn.mm"
include "sylanbrc.mm"

theorem cnvtsr
  let cR: class R


  assert |- ( R e. TosetRel -> `' R e. TosetRel )

  proof
    cR
    ctsr
    wcel
    #
    cR
    ccnv
    #
    cps
    wcel
    #
    cR
    crn
    #
    @3
    cxp
    #
    @1
    @1
    ccnv
    #
    cun
    #
    wss
    @1
    ctsr
    wcel
    @0
    cR
    cps
    wcel
    #
    @2
    cR
    tsrps
    #
    cR
    cnvps
    syl
    @0
    cR
    cdm
    #
    @9
    cxp
    #
    cR
    @1
    cun
    #
    @4
    @6
    @0
    @7
    @10
    @11
    wss
    cR
    @9
    @9
    eqid
    #
    istsr
    simprbi
    @0
    @9
    @3
    @0
    @7
    @9
    @3
    wceq
    @8
    cR
    @9
    @12
    psrn
    syl
    sqxpeqd
    @0
    @6
    @1
    cR
    cun
    @11
    @0
    @5
    cR
    @1
    @0
    cR
    wrel
    #
    @5
    cR
    wceq
    @0
    @7
    @13
    @8
    cR
    psrel
    syl
    cR
    dfrel2
    sylib
    uneq2d
    @1
    cR
    uncom
    syl6req
    3sstr3d
    @1
    @3
    cR
    df-rn
    istsr
    sylanbrc
end
