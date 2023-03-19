include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "choccli.mm"
include "pjoml2i.mm"
include "chsscon3i.mm"
include "eqcom.mm"
include "chincli.mm"
include "chdmj2i.mm"
include "chdmm4i.mm"
include "ineq2i.mm"
include "eqtri.mm"
include "eqeq1i.mm"
include "chjcli.mm"
include "chcon2i.mm"
include "3bitr3i.mm"
include "3imtr4i.mm"

theorem pjoml3i
  let cA: class A
  let cB: class B
  let vx: setvar x
  assume pjoml2.1: |- A e. CH
  assume pjoml2.2: |- B e. CH


  assert |- ( B C_ A -> ( A i^i ( ( _|_ ` A ) vH B ) ) = B )

  proof
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    wss
    @0
    @0
    cort
    cfv
    #
    @1
    cin
    #
    chj
    co
    #
    @1
    wceq
    #
    cB
    cA
    wss
    cA
    @0
    cB
    chj
    co
    #
    cin
    #
    cB
    wceq
    #
    @0
    @1
    cA
    pjoml2.1
    choccli
    #
    cB
    pjoml2.2
    choccli
    #
    pjoml2i
    cB
    cA
    pjoml2.2
    pjoml2.1
    chsscon3i
    @4
    cort
    cfv
    #
    cB
    wceq
    cB
    @11
    wceq
    @8
    @5
    @11
    cB
    eqcom
    @11
    @7
    cB
    @11
    cA
    @3
    cort
    cfv
    #
    cin
    @7
    cA
    @3
    pjoml2.1
    @2
    @1
    @0
    @9
    choccli
    @10
    chincli
    #
    chdmj2i
    @12
    @6
    cA
    @0
    cB
    @9
    pjoml2.2
    chdmm4i
    ineq2i
    eqtri
    eqeq1i
    cB
    @4
    pjoml2.2
    @0
    @3
    @9
    @13
    chjcli
    chcon2i
    3bitr3i
    3imtr4i
end
