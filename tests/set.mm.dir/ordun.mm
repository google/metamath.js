include "word.mm"
include "wa.mm"
include "cun.mm"
include "wceq.mm"
include "wo.mm"
include "eqid.mm"
include "ordequn.mm"
include "mpi.mm"
include "ordeq.mm"
include "biimprcd.mm"
include "jaao.mm"
include "mpd.mm"

theorem ordun
  let cA: class A
  let cB: class B


  assert |- ( ( Ord A /\ Ord B ) -> Ord ( A u. B ) )

  proof
    cA
    word
    #
    cB
    word
    #
    wa
    #
    cA
    cB
    cun
    #
    cA
    wceq
    #
    @3
    cB
    wceq
    #
    wo
    #
    @3
    word
    #
    @2
    @3
    @3
    wceq
    @6
    @3
    eqid
    @3
    cA
    cB
    ordequn
    mpi
    @0
    @4
    @7
    @1
    @5
    @4
    @7
    @0
    @3
    cA
    ordeq
    biimprcd
    @5
    @7
    @1
    @3
    cB
    ordeq
    biimprcd
    jaao
    mpd
end
