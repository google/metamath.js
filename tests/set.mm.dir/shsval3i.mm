include "cph.mm"
include "co.mm"
include "cun.mm"
include "cv.mm"
include "wss.mm"
include "csh.mm"
include "crab.mm"
include "cint.mm"
include "cspn.mm"
include "cfv.mm"
include "shsval2i.mm"
include "chil.mm"
include "wceq.mm"
include "shssii.mm"
include "unssi.mm"
include "spanval.mm"
include "ax-mp.mm"
include "eqtr4i.mm"

theorem shsval3i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume shlesb1.1: |- A e. SH
  assume shlesb1.2: |- B e. SH


  assert |- ( A +H B ) = ( span ` ( A u. B ) )

  proof
    cA
    cB
    cph
    co
    cA
    cB
    cun
    #
    vx
    cv
    wss
    vx
    csh
    crab
    cint
    #
    @0
    cspn
    cfv
    #
    vx
    cA
    cB
    shlesb1.1
    shlesb1.2
    shsval2i
    @0
    chil
    wss
    @2
    @1
    wceq
    cA
    cB
    chil
    cA
    shlesb1.1
    shssii
    cB
    shlesb1.2
    shssii
    unssi
    vx
    @0
    spanval
    ax-mp
    eqtr4i
end
