include "cop.mm"
include "cuni.mm"
include "csn.mm"
include "cpr.mm"
include "cun.mm"
include "dfop.mm"
include "unieqi.mm"
include "snex.mm"
include "prex.mm"
include "unipr.mm"
include "wss.mm"
include "wceq.mm"
include "snsspr1.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "3eqtri.mm"

theorem uniop
  let cA: class A
  let cB: class B
  assume opthw.1: |- A e. _V
  assume opthw.2: |- B e. _V


  assert |- U. <. A , B >. = { A , B }

  proof
    cA
    cB
    cop
    #
    cuni
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    cuni
    @1
    @2
    cun
    #
    @2
    @0
    @3
    cA
    cB
    opthw.1
    opthw.2
    dfop
    unieqi
    @1
    @2
    cA
    snex
    cA
    cB
    prex
    unipr
    @1
    @2
    wss
    @4
    @2
    wceq
    cA
    cB
    snsspr1
    @1
    @2
    ssequn1
    mpbi
    3eqtri
end
