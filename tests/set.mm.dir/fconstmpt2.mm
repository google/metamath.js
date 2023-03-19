include "cxp.mm"
include "csn.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "fconstmpt.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "eqidd.mm"
include "mpt2mpt.mm"
include "eqtri.mm"

theorem fconstmpt2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vz: setvar z

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint A z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint C z
  assert |- ( ( A X. B ) X. { C } ) = ( x e. A , y e. B |-> C )

  proof
    cA
    cB
    cxp
    #
    cC
    csn
    cxp
    vz
    @0
    cC
    cmpt
    vx
    vy
    cA
    cB
    cC
    cmpt2
    vz
    @0
    cC
    fconstmpt
    vx
    vy
    vz
    cA
    cB
    cC
    cC
    vz
    cv
    vx
    cv
    vy
    cv
    cop
    wceq
    cC
    eqidd
    mpt2mpt
    eqtri
end
