include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "cuni.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "dfral2.mm"
include "wi.mm"
include "wa.mm"
include "ciun.mm"
include "iunfi.mm"
include "iunin2.mm"
include "eleq1i.mm"
include "uniiun.mm"
include "eqcomi.mm"
include "ineq2i.mm"
include "wceq.mm"
include "df-ss.mm"
include "eleq1.mm"
include "pm2.24.mm"
include "syl6bi.mm"
include "sylbi.mm"
include "com12.mm"
include "syl.mm"
include "ex.mm"
include "com24.mm"
include "3imp.mm"
include "syl5bir.mm"
include "pm2.18d.mm"

theorem infssuni
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( -. A e. Fin /\ B e. Fin /\ A C_ U. B ) -> E. x e. B -. ( A i^i x ) e. Fin )

  proof
    cA
    cfn
    wcel
    #
    wn
    #
    cB
    cfn
    wcel
    #
    cA
    cB
    cuni
    #
    wss
    #
    w3a
    #
    cA
    vx
    cv
    #
    cin
    #
    cfn
    wcel
    #
    wn
    vx
    cB
    wrex
    #
    @9
    wn
    @8
    vx
    cB
    wral
    #
    @5
    @9
    @8
    vx
    cB
    dfral2
    @1
    @2
    @4
    @10
    @9
    wi
    #
    @2
    @1
    @4
    @11
    wi
    @2
    @10
    @4
    @1
    @9
    @2
    @10
    @4
    @1
    @9
    wi
    #
    wi
    #
    @2
    @10
    wa
    vx
    cB
    @7
    ciun
    #
    cfn
    wcel
    #
    @13
    vx
    cB
    @7
    iunfi
    @15
    cA
    vx
    cB
    @6
    ciun
    #
    cin
    #
    cfn
    wcel
    #
    @13
    @14
    @17
    cfn
    vx
    cB
    cA
    @6
    iunin2
    eleq1i
    @18
    cA
    @3
    cin
    #
    cfn
    wcel
    #
    @13
    @17
    @19
    cfn
    @16
    @3
    cA
    @3
    @16
    vx
    cB
    uniiun
    eqcomi
    ineq2i
    eleq1i
    @4
    @20
    @12
    @4
    @19
    cA
    wceq
    #
    @20
    @12
    wi
    cA
    @3
    df-ss
    @21
    @20
    @0
    @12
    @19
    cA
    cfn
    eleq1
    @0
    @9
    pm2.24
    syl6bi
    sylbi
    com12
    sylbi
    sylbi
    syl
    ex
    com24
    com12
    3imp
    syl5bir
    pm2.18d
end
