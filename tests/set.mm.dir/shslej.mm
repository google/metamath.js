include "csh.mm"
include "wcel.mm"
include "cph.mm"
include "co.mm"
include "chj.mm"
include "wss.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "oveq1.mm"
include "sseq12d.mm"
include "oveq2.mm"
include "helsh.mm"
include "elimel.mm"
include "shsleji.mm"
include "dedth2h.mm"

theorem shslej
  let cA: class A
  let cB: class B


  assert |- ( ( A e. SH /\ B e. SH ) -> ( A +H B ) C_ ( A vH B ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
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
    @0
    cA
    chil
    cif
    #
    cB
    cph
    co
    #
    @4
    cB
    chj
    co
    #
    wss
    @4
    @1
    cB
    chil
    cif
    #
    cph
    co
    #
    @4
    @7
    chj
    co
    #
    wss
    cA
    cB
    chil
    chil
    cA
    @4
    wceq
    @2
    @5
    @3
    @6
    cA
    @4
    cB
    cph
    oveq1
    cA
    @4
    cB
    chj
    oveq1
    sseq12d
    cB
    @7
    wceq
    @5
    @8
    @6
    @9
    cB
    @7
    @4
    cph
    oveq2
    cB
    @7
    @4
    chj
    oveq2
    sseq12d
    @4
    @7
    cA
    chil
    csh
    helsh
    elimel
    cB
    chil
    csh
    helsh
    elimel
    shsleji
    dedth2h
end
