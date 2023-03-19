include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "ltadd2.mm"
include "simp3.mm"
include "recnd.mm"
include "simp1.mm"
include "addcomd.mm"
include "simp2.mm"
include "breq12d.mm"
include "bitrd.mm"

theorem ltadd1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A < B <-> ( A + C ) < ( B + C ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    cC
    cA
    caddc
    co
    #
    cC
    cB
    caddc
    co
    #
    clt
    wbr
    cA
    cC
    caddc
    co
    #
    cB
    cC
    caddc
    co
    #
    clt
    wbr
    cA
    cB
    cC
    ltadd2
    @3
    @4
    @6
    @5
    @7
    clt
    @3
    cC
    cA
    @3
    cC
    @0
    @1
    @2
    simp3
    recnd
    #
    @3
    cA
    @0
    @1
    @2
    simp1
    recnd
    addcomd
    @3
    cC
    cB
    @8
    @3
    cB
    @0
    @1
    @2
    simp2
    recnd
    addcomd
    breq12d
    bitrd
end
