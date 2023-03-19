include "cres.mm"
include "wcel.mm"
include "cqs.mm"
include "cuni.mm"
include "cima.mm"
include "crn.mm"
include "uniqsALTV.mm"
include "df-ima.mm"
include "syl6req.mm"

theorem rnresequniqs
  let cA: class A
  let cR: class R
  let cV: class V


  assert |- ( ( R |` A ) e. V -> ran ( R |` A ) = U. ( A /. R ) )

  proof
    cR
    cA
    cres
    #
    cV
    wcel
    cA
    cR
    cqs
    cuni
    cR
    cA
    cima
    @0
    crn
    cA
    cR
    cV
    uniqsALTV
    cR
    cA
    df-ima
    syl6req
end
