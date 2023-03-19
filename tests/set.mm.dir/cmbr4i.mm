include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wss.mm"
include "cmbr3i.mm"
include "inss2.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "wa.mm"
include "inss1.mm"
include "jctl.mm"
include "ssin.mm"
include "sylib.mm"
include "choccli.mm"
include "chub2i.mm"
include "sslin.mm"
include "ax-mp.mm"
include "jctir.mm"
include "eqss.mm"
include "sylibr.mm"
include "impbii.mm"
include "bitri.mm"

theorem cmbr4i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A C_H B <-> ( A i^i ( ( _|_ ` A ) vH B ) ) C_ B )

  proof
    cA
    cB
    ccm
    wbr
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
    @2
    cB
    wss
    #
    cA
    cB
    pjoml2.1
    pjoml2.2
    cmbr3i
    @4
    @5
    @4
    @5
    @3
    cB
    wss
    cA
    cB
    inss2
    @2
    @3
    cB
    sseq1
    mpbiri
    @5
    @2
    @3
    wss
    #
    @3
    @2
    wss
    #
    wa
    @4
    @5
    @6
    @7
    @5
    @2
    cA
    wss
    #
    @5
    wa
    @6
    @5
    @8
    cA
    @1
    inss1
    jctl
    @2
    cA
    cB
    ssin
    sylib
    cB
    @1
    wss
    @7
    cB
    @0
    pjoml2.2
    cA
    pjoml2.1
    choccli
    chub2i
    cB
    @1
    cA
    sslin
    ax-mp
    jctir
    @2
    @3
    eqss
    sylibr
    impbii
    bitri
end
