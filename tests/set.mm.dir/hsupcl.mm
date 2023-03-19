include "chil.mm"
include "cpw.mm"
include "wss.mm"
include "chsup.mm"
include "cfv.mm"
include "cuni.mm"
include "cort.mm"
include "cch.mm"
include "hsupval.mm"
include "wcel.mm"
include "sspwuni.mm"
include "ocss.mm"
include "occl.mm"
include "syl.mm"
include "sylbi.mm"
include "eqeltrd.mm"

theorem hsupcl
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A C_ ~P ~H -> ( \/H ` A ) e. CH )

  proof
    cA
    chil
    cpw
    wss
    #
    cA
    chsup
    cfv
    cA
    cuni
    #
    cort
    cfv
    #
    cort
    cfv
    #
    cch
    cA
    hsupval
    @0
    @1
    chil
    wss
    #
    @3
    cch
    wcel
    #
    cA
    chil
    sspwuni
    @4
    @2
    chil
    wss
    @5
    @1
    ocss
    @2
    occl
    syl
    sylbi
    eqeltrd
end
