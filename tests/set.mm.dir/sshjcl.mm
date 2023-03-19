include "chil.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "cch.mm"
include "sshjval.mm"
include "wcel.mm"
include "unss.mm"
include "ocss.mm"
include "occl.mm"
include "syl.mm"
include "sylbi.mm"
include "eqeltrd.mm"

theorem sshjcl
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ ~H /\ B C_ ~H ) -> ( A vH B ) e. CH )

  proof
    cA
    chil
    wss
    cB
    chil
    wss
    wa
    #
    cA
    cB
    chj
    co
    cA
    cB
    cun
    #
    cort
    cfv
    #
    cort
    cfv
    #
    cch
    cA
    cB
    sshjval
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
    cB
    chil
    unss
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
