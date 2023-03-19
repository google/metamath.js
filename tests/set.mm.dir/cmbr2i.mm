include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "cmcm4i.mm"
include "choccli.mm"
include "cmbri.mm"
include "eqcom.mm"
include "chjcli.mm"
include "chincli.mm"
include "chcon3i.mm"
include "chdmm1i.mm"
include "chdmj1i.mm"
include "oveq12i.mm"
include "eqtri.mm"
include "eqeq2i.mm"
include "3bitrri.mm"
include "3bitri.mm"

theorem cmbr2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_H B <-> A = ( ( A vH B ) i^i ( A vH ( _|_ ` B ) ) ) )

  proof
    cA
    cB
    ccm
    wbr
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    ccm
    wbr
    @0
    @0
    @1
    cin
    #
    @0
    @1
    cort
    cfv
    cin
    #
    chj
    co
    #
    wceq
    #
    cA
    cA
    cB
    chj
    co
    #
    cA
    @1
    chj
    co
    #
    cin
    #
    wceq
    #
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmcm4i
    @0
    @1
    cA
    pjoml2.1
    choccli
    cB
    pjoml2.2
    choccli
    #
    cmbri
    @9
    @8
    cA
    wceq
    @0
    @8
    cort
    cfv
    #
    wceq
    @5
    cA
    @8
    eqcom
    @8
    cA
    @6
    @7
    cA
    cB
    pjoml2.1
    pjoml2.2
    chjcli
    #
    cA
    @1
    pjoml2.1
    @10
    chjcli
    #
    chincli
    pjoml2.1
    chcon3i
    @11
    @4
    @0
    @11
    @6
    cort
    cfv
    #
    @7
    cort
    cfv
    #
    chj
    co
    @4
    @6
    @7
    @12
    @13
    chdmm1i
    @14
    @2
    @15
    @3
    chj
    cA
    cB
    pjoml2.1
    pjoml2.2
    chdmj1i
    cA
    @1
    pjoml2.1
    @10
    chdmj1i
    oveq12i
    eqtri
    eqeq2i
    3bitrri
    3bitri
end
