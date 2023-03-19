include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "cmcmi.mm"
include "cmbr2i.mm"
include "bitri.mm"
include "ineq2.mm"
include "inass.mm"
include "chjcomi.mm"
include "ineq2i.mm"
include "chabs2i.mm"
include "eqtri.mm"
include "choccli.mm"
include "ineq12i.mm"
include "eqtr3i.mm"
include "syl6req.mm"
include "sylbi.mm"
include "wss.mm"
include "inss1.mm"
include "chincli.mm"
include "pjoml2i.mm"
include "ax-mp.mm"
include "chdmm3i.mm"
include "incom.mm"
include "eqeq1i.mm"
include "oveq1.mm"
include "syl5eq.mm"
include "cmbri.mm"
include "sylibr.mm"
include "impbii.mm"

theorem cmbr3i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_H B <-> ( A i^i ( ( _|_ ` A ) vH B ) ) = ( A i^i B ) )

  proof
    cA
    cB
    ccm
    wbr
    #
    cA
    cA
    cort
    cfv
    #
    cB
    chj
    co
    #
    cin
    #
    cA
    cB
    cin
    #
    wceq
    #
    @0
    cB
    cB
    cA
    chj
    co
    #
    cB
    @1
    chj
    co
    #
    cin
    #
    wceq
    #
    @5
    @0
    cB
    cA
    ccm
    wbr
    @9
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmcmi
    cB
    cA
    pjoml2.2
    pjoml2.1
    cmbr2i
    bitri
    @9
    @4
    cA
    @8
    cin
    #
    @3
    cB
    @8
    cA
    ineq2
    cA
    @6
    cin
    #
    @7
    cin
    @10
    @3
    cA
    @6
    @7
    inass
    @11
    cA
    @7
    @2
    @11
    cA
    cA
    cB
    chj
    co
    #
    cin
    cA
    @6
    @12
    cA
    cB
    cA
    pjoml2.2
    pjoml2.1
    chjcomi
    ineq2i
    cA
    cB
    pjoml2.1
    pjoml2.2
    chabs2i
    eqtri
    cB
    @1
    pjoml2.2
    cA
    pjoml2.1
    choccli
    chjcomi
    ineq12i
    eqtr3i
    syl6req
    sylbi
    @5
    cA
    @4
    cA
    cB
    cort
    cfv
    #
    cin
    #
    chj
    co
    #
    wceq
    @0
    @5
    cA
    @14
    cort
    cfv
    #
    cA
    cin
    #
    @14
    chj
    co
    #
    @15
    @14
    @17
    chj
    co
    #
    cA
    @18
    @14
    cA
    wss
    @19
    cA
    wceq
    cA
    @13
    inss1
    @14
    cA
    cA
    @13
    pjoml2.1
    cB
    pjoml2.2
    choccli
    chincli
    #
    pjoml2.1
    pjoml2i
    ax-mp
    @14
    @17
    @20
    @16
    cA
    @14
    @20
    choccli
    pjoml2.1
    chincli
    chjcomi
    eqtr3i
    @5
    @17
    @4
    wceq
    @18
    @15
    wceq
    @3
    @17
    @4
    cA
    @16
    cin
    @3
    @17
    @16
    @2
    cA
    cA
    cB
    pjoml2.1
    pjoml2.2
    chdmm3i
    ineq2i
    cA
    @16
    incom
    eqtr3i
    eqeq1i
    @17
    @4
    @14
    chj
    oveq1
    sylbi
    syl5eq
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmbri
    sylibr
    impbii
end
