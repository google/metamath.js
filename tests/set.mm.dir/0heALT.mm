include "c0.mm"
include "cxp.mm"
include "whe.mm"
include "xphe.mm"
include "wceq.mm"
include "wb.mm"
include "0xp.mm"
include "heeq1.mm"
include "ax-mp.mm"
include "mpbi.mm"

theorem 0heALT
  let cA: class A


  assert |- (/) hereditary A

  proof
    cA
    c0
    cA
    cxp
    #
    whe
    #
    cA
    c0
    whe
    #
    c0
    cA
    xphe
    @0
    c0
    wceq
    @1
    @2
    wb
    cA
    0xp
    cA
    @0
    c0
    heeq1
    ax-mp
    mpbi
end
