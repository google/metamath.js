include "con0.mm"
include "wcel.mm"
include "coa.mm"
include "co.mm"
include "wss.mm"
include "wa.mm"
include "c0.mm"
include "0ss.mm"
include "wi.mm"
include "0elon.mm"
include "oawordri.mm"
include "mp3an1.mm"
include "wceq.mm"
include "oa0r.mm"
include "adantl.mm"
include "sseq1d.mm"
include "sylibd.mm"
include "mpi.mm"
include "ancoms.mm"

theorem oaword2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> A C_ ( B +o A ) )

  proof
    cB
    con0
    wcel
    #
    cA
    con0
    wcel
    #
    cA
    cB
    cA
    coa
    co
    #
    wss
    #
    @0
    @1
    wa
    #
    c0
    cB
    wss
    #
    @3
    cB
    0ss
    @4
    @5
    c0
    cA
    coa
    co
    #
    @2
    wss
    #
    @3
    c0
    con0
    wcel
    @0
    @1
    @5
    @7
    wi
    0elon
    c0
    cB
    cA
    oawordri
    mp3an1
    @4
    @6
    cA
    @2
    @1
    @6
    cA
    wceq
    @0
    cA
    oa0r
    adantl
    sseq1d
    sylibd
    mpi
    ancoms
end
