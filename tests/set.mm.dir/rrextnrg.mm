include "crrext.mm"
include "wcel.mm"
include "cnrg.mm"
include "cdr.mm"
include "wa.mm"
include "czlm.mm"
include "cfv.mm"
include "cnlm.mm"
include "cchr.mm"
include "cc0.mm"
include "wceq.mm"
include "ccusp.mm"
include "cuss.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmetu.mm"
include "eqid.mm"
include "isrrext.mm"
include "simp1bi.mm"
include "simpld.mm"

theorem rrextnrg
  let cR: class R


  assert |- ( R e. RRExt -> R e. NrmRing )

  proof
    cR
    crrext
    wcel
    #
    cR
    cnrg
    wcel
    #
    cR
    cdr
    wcel
    #
    @0
    @1
    @2
    wa
    cR
    czlm
    cfv
    #
    cnlm
    wcel
    cR
    cchr
    cfv
    cc0
    wceq
    wa
    cR
    ccusp
    wcel
    cR
    cuss
    cfv
    cR
    cds
    cfv
    cR
    cbs
    cfv
    #
    @4
    cxp
    cres
    #
    cmetu
    cfv
    wceq
    wa
    @4
    @5
    cR
    @3
    @4
    eqid
    @5
    eqid
    @3
    eqid
    isrrext
    simp1bi
    simpld
end
