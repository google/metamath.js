include "cop.mm"
include "cint.mm"
include "csn.mm"
include "cpr.mm"
include "dfop.mm"
include "inteqi.mm"
include "cin.mm"
include "snex.mm"
include "prex.mm"
include "intpr.mm"
include "wss.mm"
include "wceq.mm"
include "snsspr1.mm"
include "df-ss.mm"
include "mpbi.mm"
include "eqtri.mm"
include "intsn.mm"

theorem op1stb
  let cA: class A
  let cB: class B
  assume op1stb.1: |- A e. _V
  assume op1stb.2: |- B e. _V


  assert |- |^| |^| <. A , B >. = A

  proof
    cA
    cB
    cop
    #
    cint
    #
    cint
    cA
    csn
    #
    cint
    cA
    @1
    @2
    @1
    @2
    cA
    cB
    cpr
    #
    cpr
    #
    cint
    #
    @2
    @0
    @4
    cA
    cB
    op1stb.1
    op1stb.2
    dfop
    inteqi
    @5
    @2
    @3
    cin
    #
    @2
    @2
    @3
    cA
    snex
    cA
    cB
    prex
    intpr
    @2
    @3
    wss
    @6
    @2
    wceq
    cA
    cB
    snsspr1
    @2
    @3
    df-ss
    mpbi
    eqtri
    eqtri
    inteqi
    cA
    op1stb.1
    intsn
    eqtri
end
