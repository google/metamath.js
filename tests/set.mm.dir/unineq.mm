include "cun.mm"
include "wceq.mm"
include "cin.mm"
include "wa.mm"
include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wi.mm"
include "eleq2.mm"
include "elin.mm"
include "3bitr3g.mm"
include "iba.mm"
include "bibi12d.mm"
include "syl5ibr.mm"
include "adantld.mm"
include "wn.mm"
include "wo.mm"
include "uncom.mm"
include "eqeq12i.mm"
include "sylbi.mm"
include "elun.mm"
include "biorf.mm"
include "adantrd.mm"
include "pm2.61i.mm"
include "eqrdv.mm"
include "uneq1.mm"
include "ineq1.mm"
include "jca.mm"
include "impbii.mm"

theorem unineq
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( ( ( A u. C ) = ( B u. C ) /\ ( A i^i C ) = ( B i^i C ) ) <-> A = B )

  proof
    cA
    cC
    cun
    #
    cB
    cC
    cun
    #
    wceq
    #
    cA
    cC
    cin
    #
    cB
    cC
    cin
    #
    wceq
    #
    wa
    #
    cA
    cB
    wceq
    #
    @6
    vx
    cA
    cB
    vx
    cv
    #
    cC
    wcel
    #
    @6
    @8
    cA
    wcel
    #
    @8
    cB
    wcel
    #
    wb
    #
    wi
    @9
    @5
    @12
    @2
    @5
    @12
    @9
    @10
    @9
    wa
    #
    @11
    @9
    wa
    #
    wb
    @5
    @8
    @3
    wcel
    @8
    @4
    wcel
    @13
    @14
    @3
    @4
    @8
    eleq2
    @8
    cA
    cC
    elin
    @8
    cB
    cC
    elin
    3bitr3g
    @9
    @10
    @13
    @11
    @14
    @9
    @10
    iba
    @9
    @11
    iba
    bibi12d
    syl5ibr
    adantld
    @9
    wn
    #
    @2
    @12
    @5
    @2
    @12
    @15
    @9
    @10
    wo
    #
    @9
    @11
    wo
    #
    wb
    @2
    @8
    cC
    cA
    cun
    #
    wcel
    #
    @8
    cC
    cB
    cun
    #
    wcel
    #
    @16
    @17
    @2
    @18
    @20
    wceq
    @19
    @21
    wb
    @0
    @18
    @1
    @20
    cA
    cC
    uncom
    cB
    cC
    uncom
    eqeq12i
    @18
    @20
    @8
    eleq2
    sylbi
    @8
    cC
    cA
    elun
    @8
    cC
    cB
    elun
    3bitr3g
    @15
    @10
    @16
    @11
    @17
    @9
    @10
    biorf
    @9
    @11
    biorf
    bibi12d
    syl5ibr
    adantrd
    pm2.61i
    eqrdv
    @7
    @2
    @5
    cA
    cB
    cC
    uneq1
    cA
    cB
    cC
    ineq1
    jca
    impbii
end
