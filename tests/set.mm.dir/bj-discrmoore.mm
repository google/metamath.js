include "cvv.mm"
include "wcel.mm"
include "cpw.mm"
include "cmoore.mm"
include "pwexg.mm"
include "cuni.mm"
include "cv.mm"
include "cint.mm"
include "cin.mm"
include "wss.mm"
include "unipw.mm"
include "ineq1i.mm"
include "inex1g.mm"
include "inss1.mm"
include "a1i.mm"
include "elpwd.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "bj-ismooredr.mm"
include "pwexr.mm"
include "impbii.mm"

theorem bj-discrmoore
  let cA: class A
  let vx: setvar x


  assert |- ( A e. _V <-> ~P A e. Moore_ )

  proof
    cA
    cvv
    wcel
    #
    cA
    cpw
    #
    cmoore
    wcel
    @0
    vx
    @1
    cvv
    cA
    cvv
    pwexg
    @0
    @1
    cuni
    #
    vx
    cv
    #
    cint
    #
    cin
    #
    @1
    wcel
    @3
    @1
    wss
    @0
    @5
    cA
    @4
    cin
    #
    @1
    @2
    cA
    @4
    cA
    unipw
    ineq1i
    @0
    @6
    cA
    cvv
    cA
    @4
    cvv
    inex1g
    @6
    cA
    wss
    @0
    cA
    @4
    inss1
    a1i
    elpwd
    syl5eqel
    adantr
    bj-ismooredr
    cA
    cmoore
    pwexr
    impbii
end
