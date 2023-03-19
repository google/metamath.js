include "crrext.mm"
include "wcel.mm"
include "ccusp.mm"
include "cuss.mm"
include "cfv.mm"
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
include "simprd.mm"

theorem rrextust
  let cB: class B
  let cD: class D
  let cR: class R
  assume rrextust.b: |- B = ( Base ` R )
  assume rrextust.d: |- D = ( ( dist ` R ) |` ( B X. B ) )


  assert |- ( R e. RRExt -> ( UnifSt ` R ) = ( metUnif ` D ) )

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
    cD
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
    @2
    wa
    cB
    cD
    cR
    @3
    rrextust.b
    rrextust.d
    @3
    eqid
    isrrext
    simp3bi
    simprd
end
