include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cfv.mm"
include "sgon.mm"
include "baselsiga.mm"
include "syl.mm"

theorem unielsiga
  let cS: class S
  let vx: setvar x


  assert |- ( S e. U. ran sigAlgebra -> U. S e. S )

  proof
    cS
    csiga
    crn
    cuni
    wcel
    cS
    cS
    cuni
    #
    csiga
    cfv
    wcel
    @0
    cS
    wcel
    cS
    sgon
    @0
    cS
    baselsiga
    syl
end
