include "cmi.mm"
include "ceq.mm"
include "cnpi.mm"
include "df-enq.mm"
include "ecopoveq.mm"

theorem enqbreq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u


  assert |- ( ( ( A e. N. /\ B e. N. ) /\ ( C e. N. /\ D e. N. ) ) -> ( <. A , B >. ~Q <. C , D >. <-> ( A .N D ) = ( B .N C ) ) )

  proof
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cB
    cC
    cD
    cmi
    ceq
    cnpi
    vx
    vy
    vz
    vw
    vv
    vu
    df-enq
    ecopoveq
end
