include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "wa.mm"
include "csx.mm"
include "co.mm"
include "cxp.mm"
include "cfv.mm"
include "wceq.mm"
include "sxsigon.mm"
include "issgon.mm"
include "simprbi.mm"
include "syl.mm"

theorem sxuni
  let cS: class S
  let cT: class T


  assert |- ( ( S e. U. ran sigAlgebra /\ T e. U. ran sigAlgebra ) -> ( U. S X. U. T ) = U. ( S sX T ) )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    cT
    @0
    wcel
    wa
    cS
    cT
    csx
    co
    #
    cS
    cuni
    cT
    cuni
    cxp
    #
    csiga
    cfv
    wcel
    #
    @2
    @1
    cuni
    wceq
    #
    cS
    cT
    sxsigon
    @3
    @1
    @0
    wcel
    @4
    @1
    @2
    issgon
    simprbi
    syl
end
