include "cz.mm"
include "wcel.mm"
include "zring.mm"
include "cnm.mm"
include "cfv.mm"
include "cabs.mm"
include "cres.mm"
include "zringnm.mm"
include "eqcomi.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5reqr.mm"

theorem zzsnm
  let cM: class M


  assert |- ( M e. ZZ -> ( abs ` M ) = ( ( norm ` ZZring ) ` M ) )

  proof
    cM
    cz
    wcel
    cM
    zring
    cnm
    cfv
    #
    cfv
    cM
    cabs
    cz
    cres
    #
    cfv
    cM
    cabs
    cfv
    cM
    @1
    @0
    @0
    @1
    zringnm
    eqcomi
    fveq1i
    cM
    cz
    cabs
    fvres
    syl5reqr
end
