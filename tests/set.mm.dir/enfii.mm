include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "enfi.mm"
include "biimparc.mm"

theorem enfii
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( B e. Fin /\ A ~~ B ) -> A e. Fin )

  proof
    cA
    cB
    cen
    wbr
    cA
    cfn
    wcel
    cB
    cfn
    wcel
    cA
    cB
    enfi
    biimparc
end
