include "bj-csngl.mm"
include "cpw.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "wex.mm"
include "csn.mm"
include "wceq.mm"
include "wrex.mm"
include "bj-elsngl.mm"
include "wa.mm"
include "df-rex.mm"
include "snssi.mm"
include "sseq1.mm"
include "biimparc.mm"
include "sylan.mm"
include "eximi.mm"
include "sylbi.mm"
include "ax5e.mm"
include "syl.mm"
include "selpw.mm"
include "sylibr.mm"
include "ssriv.mm"

theorem bj-snglss
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- sngl A C_ ~P A

  proof
    vx
    cA
    bj-csngl
    #
    cA
    cpw
    #
    vx
    cv
    #
    @0
    wcel
    #
    @2
    cA
    wss
    #
    @2
    @1
    wcel
    @3
    @4
    vy
    wex
    #
    @4
    @3
    @2
    vy
    cv
    #
    csn
    #
    wceq
    #
    vy
    cA
    wrex
    #
    @5
    vy
    @2
    cA
    bj-elsngl
    @9
    @6
    cA
    wcel
    #
    @8
    wa
    #
    vy
    wex
    @5
    @8
    vy
    cA
    df-rex
    @11
    @4
    vy
    @10
    @7
    cA
    wss
    #
    @8
    @4
    @6
    cA
    snssi
    @8
    @4
    @12
    @2
    @7
    cA
    sseq1
    biimparc
    sylan
    eximi
    sylbi
    sylbi
    @4
    vy
    ax5e
    syl
    vx
    cA
    selpw
    sylibr
    ssriv
end
