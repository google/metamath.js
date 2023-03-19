include "cep.mm"
include "ccnv.mm"
include "cres.mm"
include "ccoss.mm"
include "cdm.mm"
include "crn.mm"
include "cuni.mm"
include "dmcoss2.mm"
include "rncnvepres.mm"
include "eqtri.mm"

theorem dm1cosscnvepres
  let cA: class A


  assert |- dom ,~ ( `' _E |` A ) = U. A

  proof
    cep
    ccnv
    cA
    cres
    #
    ccoss
    cdm
    @0
    crn
    cA
    cuni
    @0
    dmcoss2
    cA
    rncnvepres
    eqtri
end
