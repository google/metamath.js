include "cin.mm"
include "chj.mm"
include "co.mm"
include "wceq.mm"
include "cort.mm"
include "cfv.mm"
include "choccli.mm"
include "cmcm3ii.mm"
include "cmcm2ii.mm"
include "fh2i.mm"
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

theorem fh4i
  let cA: class A
  let cB: class B
  let cC: class C
  assume fh1.1: |- A e. CH
  assume fh1.2: |- B e. CH
  assume fh1.3: |- C e. CH
  assume fh1.4: |- A C_H B
  assume fh1.5: |- A C_H C


  assert |- ( B vH ( A i^i C ) ) = ( ( B vH A ) i^i ( B vH C ) )

  proof
    cB
    cA
    cC
    cin
    #
    chj
    co
    #
    cB
    cA
    chj
    co
    #
    cB
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
    cB
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
    cA
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
    @13
    @10
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
    @13
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
    @13
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
    fh2i
    @11
    @15
    @10
    cA
    cC
    fh1.1
    fh1.3
    chdmm1i
    ineq2i
    @7
    @16
    @8
    @17
    chj
    cB
    cA
    fh1.2
    fh1.1
    chdmj1i
    cB
    cC
    fh1.2
    fh1.3
    chdmj1i
    oveq12i
    3eqtr4ri
    @2
    @3
    cB
    cA
    fh1.2
    fh1.1
    chjcli
    #
    cB
    cC
    fh1.2
    fh1.3
    chjcli
    #
    chdmm1i
    cB
    @0
    fh1.2
    cA
    cC
    fh1.1
    fh1.3
    chincli
    #
    chdmj1i
    3eqtr4i
    @1
    @4
    cB
    @0
    fh1.2
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
