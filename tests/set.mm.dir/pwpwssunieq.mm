include "cv.mm"
include "cuni.mm"
include "wceq.mm"
include "cab.mm"
include "wss.mm"
include "cpw.mm"
include "eqimss.mm"
include "ss2abi.mm"
include "pwpwab.mm"
include "sseqtr4i.mm"

theorem pwpwssunieq
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- { x | U. x = A } C_ ~P ~P A

  proof
    vx
    cv
    cuni
    #
    cA
    wceq
    #
    vx
    cab
    @0
    cA
    wss
    #
    vx
    cab
    cA
    cpw
    cpw
    @1
    @2
    vx
    @0
    cA
    eqimss
    ss2abi
    vx
    cA
    pwpwab
    sseqtr4i
end
