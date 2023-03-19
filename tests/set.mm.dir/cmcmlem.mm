include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "ccm.mm"
include "wbr.mm"
include "wss.mm"
include "choccli.mm"
include "chub2i.mm"
include "sseqin2.mm"
include "mpbi.mm"
include "ineq2i.mm"
include "inass.mm"
include "chdmm1i.mm"
include "ineq1i.mm"
include "3eqtr4ri.mm"
include "chdmj4i.mm"
include "chdmj2i.mm"
include "oveq12i.mm"
include "eqeq2i.mm"
include "biimpri.mm"
include "fveq2d.mm"
include "chjcli.mm"
include "syl6req.mm"
include "ineq1d.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "inss2.mm"
include "chincli.mm"
include "pjoml2i.mm"
include "ax-mp.mm"
include "incom.mm"
include "3eqtr3g.mm"
include "cmbri.mm"
include "3imtr4i.mm"

theorem cmcmlem
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_H B -> B C_H A )

  proof
    cA
    cA
    cB
    cin
    #
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
    #
    cB
    cB
    cA
    cin
    #
    cB
    cA
    cort
    cfv
    #
    cin
    #
    chj
    co
    #
    wceq
    cA
    cB
    ccm
    wbr
    cB
    cA
    ccm
    wbr
    @4
    @0
    @0
    cort
    cfv
    #
    cB
    cin
    #
    chj
    co
    #
    @0
    @6
    cB
    cin
    #
    chj
    co
    cB
    @8
    @4
    @10
    @12
    @0
    chj
    @4
    @10
    @6
    @1
    chj
    co
    #
    @6
    cB
    chj
    co
    #
    cin
    #
    cB
    cin
    #
    @12
    @13
    @14
    cB
    cin
    #
    cin
    @13
    cB
    cin
    @16
    @10
    @17
    cB
    @13
    cB
    @14
    wss
    @17
    cB
    wceq
    cB
    @6
    pjoml2.2
    cA
    pjoml2.1
    choccli
    #
    chub2i
    cB
    @14
    sseqin2
    mpbi
    ineq2i
    @13
    @14
    cB
    inass
    @9
    @13
    cB
    cA
    cB
    pjoml2.1
    pjoml2.2
    chdmm1i
    ineq1i
    3eqtr4ri
    @4
    @15
    @6
    cB
    @4
    @6
    @13
    cort
    cfv
    #
    @14
    cort
    cfv
    #
    chj
    co
    #
    cort
    cfv
    @15
    @4
    cA
    @21
    cort
    cA
    @21
    wceq
    @4
    @21
    @3
    cA
    @19
    @0
    @20
    @2
    chj
    cA
    cB
    pjoml2.1
    pjoml2.2
    chdmj4i
    cA
    cB
    pjoml2.1
    pjoml2.2
    chdmj2i
    oveq12i
    eqeq2i
    biimpri
    fveq2d
    @13
    @14
    @6
    @1
    @18
    cB
    pjoml2.2
    choccli
    chjcli
    @6
    cB
    @18
    pjoml2.2
    chjcli
    chdmj4i
    syl6req
    ineq1d
    syl5eq
    oveq2d
    @0
    cB
    wss
    @11
    cB
    wceq
    cA
    cB
    inss2
    @0
    cB
    cA
    cB
    pjoml2.1
    pjoml2.2
    chincli
    pjoml2.2
    pjoml2i
    ax-mp
    @0
    @5
    @12
    @7
    chj
    cA
    cB
    incom
    @6
    cB
    incom
    oveq12i
    3eqtr3g
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmbri
    cB
    cA
    pjoml2.2
    pjoml2.1
    cmbri
    3imtr4i
end
