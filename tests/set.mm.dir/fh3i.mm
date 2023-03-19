include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "choccli.mm"
include "cmcm3ii.mm"
include "cmcm2ii.mm"
include "fh1i.mm"
include "chdmm1i.mm"
include "ineq2i.mm"
include "chdmj1i.mm"
include "oveq12i.mm"
include "3eqtr4ri.mm"
include "chjcli.mm"
include "chincli.mm"
include "3eqtr4i.mm"
include "chcon3i.mm"
include "mpbir.mm"

theorem fh3i
  let cA: class A
  let cB: class B
  let cC: class C
  assume fh1.1: |- A e. CH
  assume fh1.2: |- B e. CH
  assume fh1.3: |- C e. CH
  assume fh1.4: |- A C_H B
  assume fh1.5: |- A C_H C


  assert |- ( A vH ( B i^i C ) ) = ( ( A vH B ) i^i ( A vH C ) )

  proof
    cA
    cB
    cC
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
    cA
    cC
    chj
    co
    #
    cin
    #
    wceq
    @4
    cort
    cfv
    #
    @1
    cort
    cfv
    #
    wceq
    @2
    cort
    cfv
    #
    @3
    cort
    cfv
    #
    chj
    co
    #
    cA
    cort
    cfv
    #
    @0
    cort
    cfv
    #
    cin
    #
    @5
    @6
    @10
    cB
    cort
    cfv
    #
    cC
    cort
    cfv
    #
    chj
    co
    #
    cin
    @10
    @13
    cin
    #
    @10
    @14
    cin
    #
    chj
    co
    @12
    @9
    @10
    @13
    @14
    cA
    fh1.1
    choccli
    #
    cB
    fh1.2
    choccli
    cC
    fh1.3
    choccli
    @10
    cB
    @18
    fh1.2
    cA
    cB
    fh1.1
    fh1.2
    fh1.4
    cmcm3ii
    cmcm2ii
    @10
    cC
    @18
    fh1.3
    cA
    cC
    fh1.1
    fh1.3
    fh1.5
    cmcm3ii
    cmcm2ii
    fh1i
    @11
    @15
    @10
    cB
    cC
    fh1.2
    fh1.3
    chdmm1i
    ineq2i
    @7
    @16
    @8
    @17
    chj
    cA
    cB
    fh1.1
    fh1.2
    chdmj1i
    cA
    cC
    fh1.1
    fh1.3
    chdmj1i
    oveq12i
    3eqtr4ri
    @2
    @3
    cA
    cB
    fh1.1
    fh1.2
    chjcli
    #
    cA
    cC
    fh1.1
    fh1.3
    chjcli
    #
    chdmm1i
    cA
    @0
    fh1.1
    cB
    cC
    fh1.2
    fh1.3
    chincli
    #
    chdmj1i
    3eqtr4i
    @1
    @4
    cA
    @0
    fh1.1
    @21
    chjcli
    @2
    @3
    @19
    @20
    chincli
    chcon3i
    mpbir
end
