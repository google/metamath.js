include "cvv.mm"
include "wcel.mm"
include "cn0.mm"
include "crelexp.mm"
include "co.mm"
include "ccnv.mm"
include "wceq.mm"
include "relexpcnv.mm"
include "ex.mm"
include "syl5com.mm"

theorem relexpcnvd
  let wph: wff ph
  let cR: class R
  let cN: class N
  assume relexpcnvd.2: |- ( ph -> R e. _V )


  assert |- ( ph -> ( N e. NN0 -> `' ( R ^r N ) = ( `' R ^r N ) ) )

  proof
    wph
    cR
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cR
    cN
    crelexp
    co
    ccnv
    cR
    ccnv
    cN
    crelexp
    co
    wceq
    #
    relexpcnvd.2
    @1
    @0
    @2
    cR
    cN
    cvv
    relexpcnv
    ex
    syl5com
end
