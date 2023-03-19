include "chl.mm"
include "wcel.mm"
include "ccnfld.mm"
include "csubrg.mm"
include "cfv.mm"
include "cress.mm"
include "co.mm"
include "cdr.mm"
include "ccms.mm"
include "ccph.mm"
include "hlcph.mm"
include "cphsubrg.mm"
include "syl.mm"
include "wceq.mm"
include "cphsca.mm"
include "clvec.mm"
include "cphlvec.mm"
include "lvecdrng.mm"
include "3syl.mm"
include "eqeltrrd.mm"
include "cbn.mm"
include "hlbn.mm"
include "bnsca.mm"
include "3jca.mm"

theorem hlprlem
  let cF: class F
  let cK: class K
  let cW: class W
  assume hlress.f: |- F = ( Scalar ` W )
  assume hlress.k: |- K = ( Base ` F )


  assert |- ( W e. CHil -> ( K e. ( SubRing ` CCfld ) /\ ( CCfld |`s K ) e. DivRing /\ ( CCfld |`s K ) e. CMetSp ) )

  proof
    cW
    chl
    wcel
    #
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    ccnfld
    cK
    cress
    co
    #
    cdr
    wcel
    @2
    ccms
    wcel
    @0
    cW
    ccph
    wcel
    #
    @1
    cW
    hlcph
    #
    cF
    cK
    cW
    hlress.f
    hlress.k
    cphsubrg
    syl
    @0
    cF
    @2
    cdr
    @0
    @3
    cF
    @2
    wceq
    @4
    cF
    cK
    cW
    hlress.f
    hlress.k
    cphsca
    syl
    #
    @0
    @3
    cW
    clvec
    wcel
    cF
    cdr
    wcel
    @4
    cW
    cphlvec
    cF
    cW
    hlress.f
    lvecdrng
    3syl
    eqeltrrd
    @0
    cF
    @2
    ccms
    @5
    @0
    cW
    cbn
    wcel
    cF
    ccms
    wcel
    cW
    hlbn
    cF
    cW
    hlress.f
    bnsca
    syl
    eqeltrrd
    3jca
end
