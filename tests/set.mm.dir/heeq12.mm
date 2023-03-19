include "wceq.mm"
include "wa.mm"
include "cima.mm"
include "wss.mm"
include "whe.mm"
include "simpl.mm"
include "simpr.mm"
include "imaeq12d.mm"
include "sseq12d.mm"
include "df-he.mm"
include "3bitr4g.mm"

theorem heeq12
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S


  assert |- ( ( R = S /\ A = B ) -> ( R hereditary A <-> S hereditary B ) )

  proof
    cR
    cS
    wceq
    #
    cA
    cB
    wceq
    #
    wa
    #
    cR
    cA
    cima
    #
    cA
    wss
    cS
    cB
    cima
    #
    cB
    wss
    cA
    cR
    whe
    cB
    cS
    whe
    @2
    @3
    @4
    cA
    cB
    @2
    cR
    cS
    cA
    cB
    @0
    @1
    simpl
    @0
    @1
    simpr
    #
    imaeq12d
    @5
    sseq12d
    cA
    cR
    df-he
    cB
    cS
    df-he
    3bitr4g
end
