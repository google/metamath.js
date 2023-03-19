include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "oa0.mm"
include "adantr.mm"
include "wss.mm"
include "0ss.mm"
include "wb.mm"
include "0elon.mm"
include "oaword.mm"
include "3com13.mm"
include "mp3an3.mm"
include "mpbii.mm"
include "eqsstr3d.mm"

theorem oaword1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> A C_ ( A +o B ) )

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
    cA
    cA
    c0
    coa
    co
    #
    cA
    cB
    coa
    co
    #
    @0
    @3
    cA
    wceq
    @1
    cA
    oa0
    adantr
    @2
    c0
    cB
    wss
    #
    @3
    @4
    wss
    #
    cB
    0ss
    @0
    @1
    c0
    con0
    wcel
    #
    @5
    @6
    wb
    #
    0elon
    @7
    @1
    @0
    @8
    c0
    cB
    cA
    oaword
    3com13
    mp3an3
    mpbii
    eqsstr3d
end
