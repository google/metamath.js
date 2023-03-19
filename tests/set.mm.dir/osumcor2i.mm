include "ccm.mm"
include "wbr.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "wss.mm"
include "wa.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "cin.mm"
include "cmcm2i.mm"
include "choccli.mm"
include "cmbr4i.mm"
include "bitri.mm"
include "chjcli.mm"
include "chincli.mm"
include "osumi.mm"
include "chjcomi.mm"
include "ineq2i.mm"
include "oveq1i.mm"
include "eqtri.mm"
include "pjoml4i.mm"
include "eqeq2i.mm"
include "inss1.mm"
include "chshii.mm"
include "shlessi.mm"
include "ax-mp.mm"
include "sseq1.mm"
include "mpbii.mm"
include "sylbi.mm"
include "syl.mm"
include "chsleji.mm"
include "jctil.mm"
include "eqss.mm"
include "sylibr.mm"

theorem osumcor2i
  let cA: class A
  let cB: class B
  assume osum.1: |- A e. CH
  assume osum.2: |- B e. CH


  assert |- ( A C_H B -> ( A +H B ) = ( A vH B ) )

  proof
    cA
    cB
    ccm
    wbr
    #
    cA
    cB
    cph
    co
    #
    cA
    cB
    chj
    co
    #
    wss
    #
    @2
    @1
    wss
    #
    wa
    @1
    @2
    wceq
    @0
    @4
    @3
    @0
    cA
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    chj
    co
    #
    cin
    #
    @6
    wss
    #
    @4
    @0
    cA
    @6
    ccm
    wbr
    @9
    cA
    cB
    osum.1
    osum.2
    cmcm2i
    cA
    @6
    osum.1
    cB
    osum.2
    choccli
    #
    cmbr4i
    bitri
    @9
    @8
    cB
    cph
    co
    #
    @8
    cB
    chj
    co
    #
    wceq
    #
    @4
    @8
    cB
    cA
    @7
    osum.1
    @5
    @6
    cA
    osum.1
    choccli
    #
    @10
    chjcli
    chincli
    #
    osum.2
    osumi
    @13
    @11
    @2
    wceq
    #
    @4
    @12
    @2
    @11
    @12
    cB
    cA
    @6
    @5
    chj
    co
    #
    cin
    #
    chj
    co
    #
    @2
    @12
    @18
    cB
    chj
    co
    @19
    @8
    @18
    cB
    chj
    @7
    @17
    cA
    @5
    @6
    @14
    @10
    chjcomi
    ineq2i
    oveq1i
    @18
    cB
    cA
    @17
    osum.1
    @6
    @5
    @10
    @14
    chjcli
    chincli
    osum.2
    chjcomi
    eqtri
    @19
    cB
    cA
    chj
    co
    @2
    cB
    cA
    osum.2
    osum.1
    pjoml4i
    cB
    cA
    osum.2
    osum.1
    chjcomi
    eqtri
    eqtri
    eqeq2i
    @16
    @11
    @1
    wss
    #
    @4
    @8
    cA
    wss
    @20
    cA
    @7
    inss1
    @8
    cA
    cB
    @8
    @15
    chshii
    cA
    osum.1
    chshii
    cB
    osum.2
    chshii
    shlessi
    ax-mp
    @11
    @2
    @1
    sseq1
    mpbii
    sylbi
    syl
    sylbi
    cA
    cB
    osum.1
    osum.2
    chsleji
    jctil
    @1
    @2
    eqss
    sylibr
end
