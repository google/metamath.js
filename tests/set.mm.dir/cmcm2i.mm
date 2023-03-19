include "cin.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "ccm.mm"
include "wbr.mm"
include "chincli.mm"
include "choccli.mm"
include "chjcomi.mm"
include "pjococi.mm"
include "ineq2i.mm"
include "oveq2i.mm"
include "eqtr4i.mm"
include "eqeq2i.mm"
include "cmbri.mm"
include "3bitr4i.mm"

theorem cmcm2i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_H B <-> A C_H ( _|_ ` B ) )

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
    cA
    @2
    cA
    @1
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
    cA
    @1
    ccm
    wbr
    @3
    @6
    cA
    @3
    @2
    @0
    chj
    co
    @6
    @0
    @2
    cA
    cB
    pjoml2.1
    pjoml2.2
    chincli
    cA
    @1
    pjoml2.1
    cB
    pjoml2.2
    choccli
    #
    chincli
    chjcomi
    @5
    @0
    @2
    chj
    @4
    cB
    cA
    cB
    pjoml2.2
    pjococi
    ineq2i
    oveq2i
    eqtr4i
    eqeq2i
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmbri
    cA
    @1
    pjoml2.1
    @7
    cmbri
    3bitr4i
end
