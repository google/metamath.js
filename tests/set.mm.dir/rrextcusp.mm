include "crrext.mm"
include "wcel.mm"
include "ccusp.mm"
include "cuss.mm"
include "cfv.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmetu.mm"
include "wceq.mm"
include "cnrg.mm"
include "cdr.mm"
include "wa.mm"
include "czlm.mm"
include "cnlm.mm"
include "cchr.mm"
include "cc0.mm"
include "eqid.mm"
include "isrrext.mm"
include "simp3bi.mm"
include "simpld.mm"

theorem rrextcusp
  let cR: class R


  assert |- ( R e. RRExt -> R e. CUnifSp )

  proof
    cR
    crrext
    wcel
    #
    cR
    ccusp
    wcel
    #
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
    @2
    cxp
    cres
    #
    cmetu
    cfv
    wceq
    #
    @0
    cR
    cnrg
    wcel
    cR
    cdr
    wcel
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
    @1
    @4
    wa
    @2
    @3
    cR
    @5
    @2
    eqid
    @3
    eqid
    @5
    eqid
    isrrext
    simp3bi
    simpld
end
