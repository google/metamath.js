include "wcel.mm"
include "cima.mm"
include "wss.mm"
include "wsbc.mm"
include "csb.mm"
include "whe.mm"
include "sbcssg.mm"
include "wceq.mm"
include "csbima12.mm"
include "a1i.mm"
include "sseq1d.mm"
include "bitrd.mm"
include "df-he.mm"
include "sbcbii.mm"
include "3bitr4g.mm"

theorem sbcheg
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( A e. V -> ( [. A / x ]. B hereditary C <-> [_ A / x ]_ B hereditary [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cC
    cima
    #
    cC
    wss
    #
    vx
    cA
    wsbc
    #
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    cima
    #
    @5
    wss
    #
    cC
    cB
    whe
    #
    vx
    cA
    wsbc
    @5
    @4
    whe
    @0
    @3
    vx
    cA
    @1
    csb
    #
    @5
    wss
    @7
    vx
    cA
    @1
    cC
    cV
    sbcssg
    @0
    @9
    @6
    @5
    @9
    @6
    wceq
    @0
    vx
    cA
    cC
    cB
    csbima12
    a1i
    sseq1d
    bitrd
    @8
    @2
    vx
    cA
    cC
    cB
    df-he
    sbcbii
    @5
    @4
    df-he
    3bitr4g
end
