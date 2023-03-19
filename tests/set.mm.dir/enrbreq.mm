include "cpp.mm"
include "cer.mm"
include "cnp.mm"
include "df-enr.mm"
include "ecopoveq.mm"

theorem enrbreq
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


  assert |- ( ( ( A e. P. /\ B e. P. ) /\ ( C e. P. /\ D e. P. ) ) -> ( <. A , B >. ~R <. C , D >. <-> ( A +P. D ) = ( B +P. C ) ) )

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
    cpp
    cer
    cnp
    vx
    vy
    vz
    vw
    vv
    vu
    df-enr
    ecopoveq
end
