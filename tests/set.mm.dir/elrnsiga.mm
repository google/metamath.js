include "csiga.mm"
include "cfv.mm"
include "crn.mm"
include "cuni.mm"
include "fvssunirn.mm"
include "sseli.mm"

theorem elrnsiga
  let cS: class S
  let cO: class O


  assert |- ( S e. ( sigAlgebra ` O ) -> S e. U. ran sigAlgebra )

  proof
    cO
    csiga
    cfv
    csiga
    crn
    cuni
    cS
    csiga
    cO
    fvssunirn
    sseli
end
