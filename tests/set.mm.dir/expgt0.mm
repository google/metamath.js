include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cz.mm"
include "cexp.mm"
include "co.mm"
include "wa.mm"
include "crp.mm"
include "elrp.mm"
include "rpexpcl.mm"
include "rpgt0d.mm"
include "sylanbr.mm"
include "3impa.mm"
include "3com23.mm"

theorem expgt0
  let cA: class A
  let cN: class N


  assert |- ( ( A e. RR /\ N e. ZZ /\ 0 < A ) -> 0 < ( A ^ N ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    cN
    cz
    wcel
    #
    cc0
    cA
    cN
    cexp
    co
    #
    clt
    wbr
    #
    @0
    @1
    @2
    @4
    @0
    @1
    wa
    cA
    crp
    wcel
    #
    @2
    @4
    cA
    elrp
    @5
    @2
    wa
    @3
    cA
    cN
    rpexpcl
    rpgt0d
    sylanbr
    3impa
    3com23
end
