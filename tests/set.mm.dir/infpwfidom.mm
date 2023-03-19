include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csn.mm"
include "cvv.mm"
include "wcel.mm"
include "snelpwi.mm"
include "snfi.mm"
include "a1i.mm"
include "elind.mm"
include "wceq.mm"
include "wb.mm"
include "sneqbg.mm"
include "adantr.mm"
include "dom2.mm"

theorem infpwfidom
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( ~P A i^i Fin ) e. _V -> A ~<_ ( ~P A i^i Fin ) )

  proof
    vx
    vy
    cA
    cA
    cpw
    #
    cfn
    cin
    vx
    cv
    #
    csn
    #
    vy
    cv
    #
    csn
    #
    cvv
    @1
    cA
    wcel
    #
    @0
    cfn
    @2
    @1
    cA
    snelpwi
    @2
    cfn
    wcel
    @5
    @1
    snfi
    a1i
    elind
    @5
    @2
    @4
    wceq
    @1
    @3
    wceq
    wb
    @3
    cA
    wcel
    @1
    @3
    cA
    sneqbg
    adantr
    dom2
end
