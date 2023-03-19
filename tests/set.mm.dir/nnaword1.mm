include "com.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "nna0.mm"
include "adantr.mm"
include "wss.mm"
include "0ss.mm"
include "wb.mm"
include "peano1.mm"
include "nnaword.mm"
include "3com13.mm"
include "mp3an3.mm"
include "mpbii.mm"
include "eqsstr3d.mm"

theorem nnaword1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> A C_ ( A +o B ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
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
    nna0
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
    com
    wcel
    #
    @5
    @6
    wb
    #
    peano1
    @7
    @1
    @0
    @8
    c0
    cB
    cA
    nnaword
    3com13
    mp3an3
    mpbii
    eqsstr3d
end
