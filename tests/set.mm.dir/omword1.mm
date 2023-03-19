include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "comu.mm"
include "co.mm"
include "wss.mm"
include "c1o.mm"
include "wb.mm"
include "word.mm"
include "eloni.mm"
include "ordgt0ge1.mm"
include "syl.mm"
include "adantl.mm"
include "wi.mm"
include "1on.mm"
include "omwordi.mm"
include "mp3an1.mm"
include "ancoms.mm"
include "wceq.mm"
include "om1.mm"
include "adantr.mm"
include "sseq1d.mm"
include "sylibd.mm"
include "sylbid.mm"
include "imp.mm"

theorem omword1
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. On /\ B e. On ) /\ (/) e. B ) -> A C_ ( A .o B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    c0
    cB
    wcel
    #
    cA
    cA
    cB
    comu
    co
    #
    wss
    #
    @2
    @3
    c1o
    cB
    wss
    #
    @5
    @1
    @3
    @6
    wb
    #
    @0
    @1
    cB
    word
    @7
    cB
    eloni
    cB
    ordgt0ge1
    syl
    adantl
    @2
    @6
    cA
    c1o
    comu
    co
    #
    @4
    wss
    #
    @5
    @1
    @0
    @6
    @9
    wi
    #
    c1o
    con0
    wcel
    @1
    @0
    @10
    1on
    c1o
    cB
    cA
    omwordi
    mp3an1
    ancoms
    @2
    @8
    cA
    @4
    @0
    @8
    cA
    wceq
    @1
    cA
    om1
    adantr
    sseq1d
    sylibd
    sylbid
    imp
end
