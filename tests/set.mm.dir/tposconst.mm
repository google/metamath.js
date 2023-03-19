include "cxp.mm"
include "csn.mm"
include "ctpos.mm"
include "cmpt2.mm"
include "fconstmpt2.mm"
include "tposmpt2.mm"
include "eqtr4i.mm"

theorem tposconst
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- tpos ( ( A X. B ) X. { C } ) = ( ( B X. A ) X. { C } )

  proof
    cA
    cB
    cxp
    cC
    csn
    #
    cxp
    #
    ctpos
    vy
    vx
    cB
    cA
    cC
    cmpt2
    cB
    cA
    cxp
    @0
    cxp
    vx
    vy
    cA
    cB
    cC
    @1
    vx
    vy
    cA
    cB
    cC
    fconstmpt2
    tposmpt2
    vy
    vx
    cB
    cA
    cC
    fconstmpt2
    eqtr4i
end
