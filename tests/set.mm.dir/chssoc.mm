include "cch.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "c0h.mm"
include "wceq.mm"
include "cin.mm"
include "inidm.mm"
include "sslin.mm"
include "syl5eqssr.mm"
include "chocin.mm"
include "sseq2d.mm"
include "chle0.mm"
include "bitrd.mm"
include "syl5ib.mm"
include "wa.mm"
include "simpr.mm"
include "choccl.mm"
include "ch0le.mm"
include "syl.mm"
include "adantr.mm"
include "eqsstrd.mm"
include "ex.mm"
include "impbid.mm"

theorem chssoc
  let cA: class A


  assert |- ( A e. CH -> ( A C_ ( _|_ ` A ) <-> A = 0H ) )

  proof
    cA
    cch
    wcel
    #
    cA
    cA
    cort
    cfv
    #
    wss
    #
    cA
    c0h
    wceq
    #
    @2
    cA
    cA
    @1
    cin
    #
    wss
    #
    @0
    @3
    @2
    cA
    cA
    cA
    cin
    @4
    cA
    inidm
    cA
    @1
    cA
    sslin
    syl5eqssr
    @0
    @5
    cA
    c0h
    wss
    @3
    @0
    @4
    c0h
    cA
    cA
    chocin
    sseq2d
    cA
    chle0
    bitrd
    syl5ib
    @0
    @3
    @2
    @0
    @3
    wa
    cA
    c0h
    @1
    @0
    @3
    simpr
    @0
    c0h
    @1
    wss
    #
    @3
    @0
    @1
    cch
    wcel
    @6
    cA
    choccl
    @1
    ch0le
    syl
    adantr
    eqsstrd
    ex
    impbid
end
