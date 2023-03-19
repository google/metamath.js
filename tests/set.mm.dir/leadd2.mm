include "cr.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "leadd1.mm"
include "simp1.mm"
include "recnd.mm"
include "simp3.mm"
include "addcomd.mm"
include "simp2.mm"
include "breq12d.mm"
include "bitrd.mm"

theorem leadd2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ C e. RR ) -> ( A <_ B <-> ( C + A ) <_ ( C + B ) ) )

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
    cle
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
    cle
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
    cle
    wbr
    cA
    cB
    cC
    leadd1
    @3
    @4
    @6
    @5
    @7
    cle
    @3
    cA
    cC
    @3
    cA
    @0
    @1
    @2
    simp1
    recnd
    @3
    cC
    @0
    @1
    @2
    simp3
    recnd
    #
    addcomd
    @3
    cB
    cC
    @3
    cB
    @0
    @1
    @2
    simp2
    recnd
    @8
    addcomd
    breq12d
    bitrd
end
