include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "wa.mm"
include "axmulgt0.mm"
include "imp.mm"
include "an4s.mm"

theorem mulgt0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) ) -> 0 < ( A x. B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    cc0
    cB
    clt
    wbr
    #
    cc0
    cA
    cB
    cmul
    co
    clt
    wbr
    #
    @0
    @1
    wa
    @2
    @3
    wa
    @4
    cA
    cB
    axmulgt0
    imp
    an4s
end
