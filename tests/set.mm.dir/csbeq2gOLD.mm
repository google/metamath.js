include "wcel.mm"
include "wceq.mm"
include "wal.mm"
include "wsbc.mm"
include "csb.mm"
include "spsbc.mm"
include "sbceqg.mm"
include "sylibd.mm"

theorem csbeq2gOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( A e. V -> ( A. x B = C -> [_ A / x ]_ B = [_ A / x ]_ C ) )

  proof
    cA
    cV
    wcel
    cB
    cC
    wceq
    #
    vx
    wal
    @0
    vx
    cA
    wsbc
    vx
    cA
    cB
    csb
    vx
    cA
    cC
    csb
    wceq
    @0
    vx
    cA
    cV
    spsbc
    vx
    cA
    cB
    cC
    cV
    sbceqg
    sylibd
end
