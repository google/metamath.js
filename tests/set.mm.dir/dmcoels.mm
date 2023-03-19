include "ccoels.mm"
include "cdm.mm"
include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "ccoss.mm"
include "cuni.mm"
include "df-coels.mm"
include "dmeqi.mm"
include "dm1cosscnvepres.mm"
include "eqtri.mm"

theorem dmcoels
  let cA: class A


  assert |- dom ~ A = U. A

  proof
    cA
    ccoels
    #
    cdm
    cep
    ccnv
    cA
    cres
    ccoss
    #
    cdm
    cA
    cuni
    @0
    @1
    cA
    df-coels
    dmeqi
    cA
    dm1cosscnvepres
    eqtri
end
