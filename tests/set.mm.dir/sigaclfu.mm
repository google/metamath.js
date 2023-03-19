include "cfn.mm"
include "wcel.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "cpw.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "fict.mm"
include "sigaclcu.mm"
include "syl3an3.mm"

theorem sigaclfu
  let cA: class A
  let cS: class S
  let vo: setvar o
  let vs: setvar s
  let vx: setvar x


  assert |- ( ( S e. U. ran sigAlgebra /\ A e. ~P S /\ A e. Fin ) -> U. A e. S )

  proof
    cA
    cfn
    wcel
    cS
    csiga
    crn
    cuni
    wcel
    cA
    cS
    cpw
    wcel
    cA
    com
    cdom
    wbr
    cA
    cuni
    cS
    wcel
    cA
    fict
    cA
    cS
    sigaclcu
    syl3an3
end
