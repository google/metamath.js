include "wlim.mm"
include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "cpw.mm"
include "wi.mm"
include "r1elwf.mm"
include "elfvdm.mm"
include "jca.mm"
include "a1i.mm"
include "pwwf.mm"
include "sylibr.mm"
include "wb.mm"
include "crnk.mm"
include "csuc.mm"
include "limsuc.mm"
include "adantr.mm"
include "wceq.mm"
include "rankpwi.mm"
include "ad2antrl.mm"
include "eleq1d.mm"
include "bitr4d.mm"
include "rankr1ag.mm"
include "adantl.mm"
include "sylanb.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem r1pwcl
  let cA: class A
  let cB: class B


  assert |- ( Lim B -> ( A e. ( R1 ` B ) <-> ~P A e. ( R1 ` B ) ) )

  proof
    cB
    wlim
    #
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cB
    cr1
    cdm
    wcel
    #
    wa
    #
    cA
    cB
    cr1
    cfv
    #
    wcel
    #
    cA
    cpw
    #
    @5
    wcel
    #
    @6
    @4
    wi
    @0
    @6
    @2
    @3
    cA
    cB
    r1elwf
    cA
    cB
    cr1
    elfvdm
    jca
    a1i
    @8
    @4
    wi
    @0
    @8
    @2
    @3
    @8
    @7
    @1
    wcel
    #
    @2
    @7
    cB
    r1elwf
    cA
    pwwf
    #
    sylibr
    @7
    cB
    cr1
    elfvdm
    jca
    a1i
    @0
    @4
    @6
    @8
    wb
    @0
    @4
    wa
    #
    cA
    crnk
    cfv
    #
    cB
    wcel
    #
    @7
    crnk
    cfv
    #
    cB
    wcel
    #
    @6
    @8
    @11
    @13
    @12
    csuc
    #
    cB
    wcel
    #
    @15
    @0
    @13
    @17
    wb
    @4
    cB
    @12
    limsuc
    adantr
    @11
    @14
    @16
    cB
    @2
    @14
    @16
    wceq
    @0
    @3
    cA
    rankpwi
    ad2antrl
    eleq1d
    bitr4d
    @4
    @6
    @13
    wb
    @0
    cA
    cB
    rankr1ag
    adantl
    @4
    @8
    @15
    wb
    #
    @0
    @2
    @9
    @3
    @18
    @10
    @7
    cB
    rankr1ag
    sylanb
    adantl
    3bitr4d
    ex
    pm5.21ndd
end
