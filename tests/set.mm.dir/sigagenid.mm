include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "csigagen.mm"
include "cfv.mm"
include "wss.mm"
include "sgon.mm"
include "ssid.mm"
include "sigagenss.mm"
include "sylancl.mm"
include "sssigagen.mm"
include "eqssd.mm"

theorem sigagenid
  let cS: class S


  assert |- ( S e. U. ran sigAlgebra -> ( sigaGen ` S ) = S )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cS
    csigagen
    cfv
    #
    cS
    @1
    cS
    cS
    cuni
    csiga
    cfv
    wcel
    cS
    cS
    wss
    @2
    cS
    wss
    cS
    sgon
    cS
    ssid
    cS
    cS
    sigagenss
    sylancl
    cS
    @0
    sssigagen
    eqssd
end
