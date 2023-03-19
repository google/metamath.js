include "wceq.mm"
include "wss.mm"
include "cdif.mm"
include "cfv.mm"
include "cpr.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "difeq2.mm"
include "fveq2.mm"
include "preq12d.mm"
include "wcel.mm"
include "prssi.mm"
include "mp2an.mm"
include "syl6eqss.mm"
include "jca.mm"

theorem kur14lem1
  let cA: class A
  let cT: class T
  let cK: class K
  let cN: class N
  let cX: class X
  assume kur14lem1.a: |- A C_ X
  assume kur14lem1.c: |- ( X \ A ) e. T
  assume kur14lem1.k: |- ( K ` A ) e. T


  assert |- ( N = A -> ( N C_ X /\ { ( X \ N ) , ( K ` N ) } C_ T ) )

  proof
    cN
    cA
    wceq
    #
    cN
    cX
    wss
    #
    cX
    cN
    cdif
    #
    cN
    cK
    cfv
    #
    cpr
    #
    cT
    wss
    @0
    @1
    cA
    cX
    wss
    kur14lem1.a
    cN
    cA
    cX
    sseq1
    mpbiri
    @0
    @4
    cX
    cA
    cdif
    #
    cA
    cK
    cfv
    #
    cpr
    #
    cT
    @0
    @2
    @5
    @3
    @6
    cN
    cA
    cX
    difeq2
    cN
    cA
    cK
    fveq2
    preq12d
    @5
    cT
    wcel
    @6
    cT
    wcel
    @7
    cT
    wss
    kur14lem1.c
    kur14lem1.k
    @5
    @6
    cT
    prssi
    mp2an
    syl6eqss
    jca
end
