include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wceq.mm"
include "cfv.mm"
include "eqid.mm"
include "wa.mm"
include "issgon.mm"
include "biimpri.mm"
include "mpan2.mm"

theorem sgon
  let cS: class S


  assert |- ( S e. U. ran sigAlgebra -> S e. ( sigAlgebra ` U. S ) )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    #
    cS
    cuni
    #
    @1
    wceq
    #
    cS
    @1
    csiga
    cfv
    wcel
    #
    @1
    eqid
    @3
    @0
    @2
    wa
    cS
    @1
    issgon
    biimpri
    mpan2
end
