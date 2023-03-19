include "cdif.mm"
include "wss.mm"
include "c0.mm"
include "wceq.mm"
include "cin.mm"
include "inidm.mm"
include "ssdifin0.mm"
include "syl5eqr.mm"
include "0ss.mm"
include "id.mm"
include "difeq2.mm"
include "sseq12d.mm"
include "mpbiri.mm"
include "impbii.mm"

theorem ssdifeq0
  let cA: class A
  let cB: class B


  assert |- ( A C_ ( B \ A ) <-> A = (/) )

  proof
    cA
    cB
    cA
    cdif
    #
    wss
    #
    cA
    c0
    wceq
    #
    @1
    cA
    cA
    cA
    cin
    c0
    cA
    inidm
    cA
    cB
    cA
    ssdifin0
    syl5eqr
    @2
    @1
    c0
    cB
    c0
    cdif
    #
    wss
    @3
    0ss
    @2
    cA
    c0
    @0
    @3
    @2
    id
    cA
    c0
    cB
    difeq2
    sseq12d
    mpbiri
    impbii
end
