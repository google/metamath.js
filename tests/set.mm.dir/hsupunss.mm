include "chil.mm"
include "cpw.mm"
include "wss.mm"
include "cuni.mm"
include "cort.mm"
include "cfv.mm"
include "chsup.mm"
include "sspwuni.mm"
include "ococss.mm"
include "sylbi.mm"
include "hsupval.mm"
include "sseqtr4d.mm"

theorem hsupunss
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ ~P ~H -> U. A C_ ( \/H ` A ) )

  proof
    cA
    chil
    cpw
    wss
    #
    cA
    cuni
    #
    @1
    cort
    cfv
    cort
    cfv
    #
    cA
    chsup
    cfv
    @0
    @1
    chil
    wss
    @1
    @2
    wss
    cA
    chil
    sspwuni
    @1
    ococss
    sylbi
    cA
    hsupval
    sseqtr4d
end
