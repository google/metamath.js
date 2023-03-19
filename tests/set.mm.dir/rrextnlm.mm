include "crrext.mm"
include "wcel.mm"
include "cnlm.mm"
include "cchr.mm"
include "cfv.mm"
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
include "simpld.mm"

theorem rrextnlm
  let cR: class R
  let cZ: class Z
  assume rrextnlm.z: |- Z = ( ZMod ` R )


  assert |- ( R e. RRExt -> Z e. NrmMod )

  proof
    cR
    crrext
    wcel
    #
    cZ
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
    @1
    @2
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
    @3
    cxp
    cres
    #
    cmetu
    cfv
    wceq
    wa
    @3
    @4
    cR
    cZ
    @3
    eqid
    @4
    eqid
    rrextnlm.z
    isrrext
    simp2bi
    simpld
end
