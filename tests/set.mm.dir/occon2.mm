include "chil.mm"
include "wss.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "ocss.mm"
include "anim12ci.mm"
include "occon.mm"
include "sylsyld.mm"

theorem occon2
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H


  assert |- ( ( A C_ ~H /\ B C_ ~H ) -> ( A C_ B -> ( _|_ ` ( _|_ ` A ) ) C_ ( _|_ ` ( _|_ ` B ) ) ) )

  proof
    cA
    chil
    wss
    #
    cB
    chil
    wss
    #
    wa
    cB
    cort
    cfv
    #
    chil
    wss
    #
    cA
    cort
    cfv
    #
    chil
    wss
    #
    wa
    cA
    cB
    wss
    @2
    @4
    wss
    @4
    cort
    cfv
    @2
    cort
    cfv
    wss
    @0
    @5
    @1
    @3
    cA
    ocss
    cB
    ocss
    anim12ci
    cA
    cB
    occon
    @2
    @4
    occon
    sylsyld
end
