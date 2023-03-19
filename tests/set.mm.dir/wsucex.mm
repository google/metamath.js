include "cwsuc.mm"
include "ccnv.mm"
include "cpred.mm"
include "cinf.mm"
include "cvv.mm"
include "df-wsuc.mm"
include "infexd.mm"
include "syl5eqel.mm"

theorem wsucex
  let wph: wff ph
  let cA: class A
  let cR: class R
  let cX: class X
  assume wsucex.1: |- ( ph -> R Or A )


  assert |- ( ph -> wsuc ( R , A , X ) e. _V )

  proof
    wph
    cA
    cR
    cX
    cwsuc
    cA
    cR
    ccnv
    cX
    cpred
    #
    cA
    cR
    cinf
    cvv
    cA
    cR
    cX
    df-wsuc
    wph
    cA
    @0
    cR
    wsucex.1
    infexd
    syl5eqel
end
