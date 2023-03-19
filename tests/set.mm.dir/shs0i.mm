include "c0h.mm"
include "cph.mm"
include "co.mm"
include "cun.mm"
include "cspn.mm"
include "cfv.mm"
include "h0elsh.mm"
include "shsval3i.mm"
include "wss.mm"
include "wceq.mm"
include "csh.mm"
include "wcel.mm"
include "sh0le.mm"
include "ax-mp.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "fveq2i.mm"
include "spanid.mm"
include "3eqtri.mm"

theorem shs0i
  let cA: class A
  let vx: setvar x
  assume shne0.1: |- A e. SH


  assert |- ( A +H 0H ) = A

  proof
    cA
    c0h
    cph
    co
    cA
    c0h
    cun
    #
    cspn
    cfv
    cA
    cspn
    cfv
    #
    cA
    cA
    c0h
    shne0.1
    h0elsh
    shsval3i
    @0
    cA
    cspn
    c0h
    cA
    wss
    #
    @0
    cA
    wceq
    cA
    csh
    wcel
    #
    @2
    shne0.1
    cA
    sh0le
    ax-mp
    c0h
    cA
    ssequn2
    mpbi
    fveq2i
    @3
    @1
    cA
    wceq
    shne0.1
    cA
    spanid
    ax-mp
    3eqtri
end
