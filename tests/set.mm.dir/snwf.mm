include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cpw.mm"
include "csn.mm"
include "pwwf.mm"
include "wss.mm"
include "snsspw.mm"
include "sswf.mm"
include "mpan2.mm"
include "sylbi.mm"

theorem snwf
  let cA: class A


  assert |- ( A e. U. ( R1 " On ) -> { A } e. U. ( R1 " On ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    cA
    cpw
    #
    @0
    wcel
    #
    cA
    csn
    #
    @0
    wcel
    #
    cA
    pwwf
    @2
    @3
    @1
    wss
    @4
    cA
    snsspw
    @1
    @3
    sswf
    mpan2
    sylbi
end
