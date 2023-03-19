include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "choccli.mm"
include "chjcli.mm"
include "chincli.mm"
include "chlej2i.mm"
include "ax-mp.mm"
include "chub1i.mm"
include "chdmm1i.mm"
include "ineq1i.mm"
include "incom.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "wceq.mm"
include "inss2.mm"
include "pjoml2i.mm"
include "eqtr3i.mm"
include "chlej1i.mm"
include "eqsstr3i.mm"
include "chlubii.mm"
include "mp2an.mm"
include "eqssi.mm"

theorem pjoml4i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( A vH ( B i^i ( ( _|_ ` A ) vH ( _|_ ` B ) ) ) ) = ( A vH B )

  proof
    cA
    cB
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
    chj
    co
    #
    cA
    cB
    chj
    co
    #
    @3
    cB
    wss
    @4
    @5
    wss
    cB
    @2
    inss1
    @3
    cB
    cA
    cB
    @2
    pjoml2.2
    @0
    @1
    cA
    pjoml2.1
    choccli
    cB
    pjoml2.2
    choccli
    chjcli
    chincli
    #
    pjoml2.2
    pjoml2.1
    chlej2i
    ax-mp
    cA
    @4
    wss
    cB
    @4
    wss
    @5
    @4
    wss
    cA
    @3
    pjoml2.1
    @6
    chub1i
    cB
    cA
    cB
    cin
    #
    @3
    chj
    co
    #
    @4
    @7
    @7
    cort
    cfv
    #
    cB
    cin
    #
    chj
    co
    #
    @8
    cB
    @10
    @3
    @7
    chj
    @10
    @2
    cB
    cin
    @3
    @9
    @2
    cB
    cA
    cB
    pjoml2.1
    pjoml2.2
    chdmm1i
    ineq1i
    @2
    cB
    incom
    eqtri
    oveq2i
    @7
    cB
    wss
    @11
    cB
    wceq
    cA
    cB
    inss2
    @7
    cB
    cA
    cB
    pjoml2.1
    pjoml2.2
    chincli
    #
    pjoml2.2
    pjoml2i
    ax-mp
    eqtr3i
    @7
    cA
    wss
    @8
    @4
    wss
    cA
    cB
    inss1
    @7
    cA
    @3
    @12
    pjoml2.1
    @6
    chlej1i
    ax-mp
    eqsstr3i
    cA
    cB
    @4
    pjoml2.1
    pjoml2.2
    cA
    @3
    pjoml2.1
    @6
    chjcli
    chlubii
    mp2an
    eqssi
end
