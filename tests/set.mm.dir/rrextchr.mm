include "crrext.mm"
include "wcel.mm"
include "czlm.mm"
include "cfv.mm"
include "cnlm.mm"
include "cchr.mm"
include "cc0.mm"
include "wceq.mm"
include "cnrg.mm"
include "cdr.mm"
include "wa.mm"
include "ccusp.mm"
include "cuss.mm"
include "cds.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cmetu.mm"
include "eqid.mm"
include "isrrext.mm"
include "simp2bi.mm"
include "simprd.mm"

theorem rrextchr
  let cR: class R


  assert |- ( R e. RRExt -> ( chr ` R ) = 0 )

  proof
    cR
    crrext
    wcel
    #
    cR
    czlm
    cfv
    #
    cnlm
    wcel
    #
    cR
    cchr
    cfv
    cc0
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
    @2
    @3
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
    @1
    @4
    eqid
    @5
    eqid
    @1
    eqid
    isrrext
    simp2bi
    simprd
end
