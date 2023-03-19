include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "char.mm"
include "csuc.mm"
include "csdm.mm"
include "ccrd.mm"
include "cdm.mm"
include "wbr.mm"
include "alephon.mm"
include "onenon.mm"
include "harsdom.mm"
include "mp2b.mm"
include "alephsuc.mm"
include "syl5breqr.mm"

theorem alephordilem1
  let cA: class A


  assert |- ( A e. On -> ( aleph ` A ) ~< ( aleph ` suc A ) )

  proof
    cA
    con0
    wcel
    cA
    cale
    cfv
    #
    @0
    char
    cfv
    #
    cA
    csuc
    cale
    cfv
    csdm
    @0
    con0
    wcel
    @0
    ccrd
    cdm
    wcel
    @0
    @1
    csdm
    wbr
    cA
    alephon
    @0
    onenon
    @0
    harsdom
    mp2b
    cA
    alephsuc
    syl5breqr
end
