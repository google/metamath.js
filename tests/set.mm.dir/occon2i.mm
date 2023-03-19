include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "wi.mm"
include "occon2.mm"
include "mp2an.mm"

theorem occon2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cH: class H
  assume occon2.1: |- A C_ ~H
  assume occon2.2: |- B C_ ~H


  assert |- ( A C_ B -> ( _|_ ` ( _|_ ` A ) ) C_ ( _|_ ` ( _|_ ` B ) ) )

  proof
    cA
    chil
    wss
    cB
    chil
    wss
    cA
    cB
    wss
    cA
    cort
    cfv
    cort
    cfv
    cB
    cort
    cfv
    cort
    cfv
    wss
    wi
    occon2.1
    occon2.2
    cA
    cB
    occon2
    mp2an
end
