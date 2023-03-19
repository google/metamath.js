include "cph.mm"
include "co.mm"
include "chj.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "cin.mm"
include "shmodsi.mm"
include "ineq1.mm"
include "sseq1d.mm"
include "syl5ib.mm"
include "imp.mm"
include "shincli.mm"
include "shsleji.mm"
include "syl6ss.mm"

theorem shmodi
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume shmod.1: |- A e. SH
  assume shmod.2: |- B e. SH
  assume shmod.3: |- C e. SH


  assert |- ( ( ( A +H B ) = ( A vH B ) /\ A C_ C ) -> ( ( A vH B ) i^i C ) C_ ( A vH ( B i^i C ) ) )

  proof
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
    wceq
    #
    cA
    cC
    wss
    #
    wa
    @1
    cC
    cin
    #
    cA
    cB
    cC
    cin
    #
    cph
    co
    #
    cA
    @5
    chj
    co
    @2
    @3
    @4
    @6
    wss
    #
    @3
    @0
    cC
    cin
    #
    @6
    wss
    @2
    @7
    cA
    cB
    cC
    shmod.1
    shmod.2
    shmod.3
    shmodsi
    @2
    @8
    @4
    @6
    @0
    @1
    cC
    ineq1
    sseq1d
    syl5ib
    imp
    cA
    @5
    shmod.1
    cB
    cC
    shmod.2
    shmod.3
    shincli
    shsleji
    syl6ss
end
