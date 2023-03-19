include "word.mm"
include "ctop.mm"
include "wcel.mm"
include "cuni.mm"
include "wne.mm"
include "eqid.mm"
include "topopn.mm"
include "nordeq.mm"
include "ex.mm"
include "syl5.mm"
include "onsuctop.mm"
include "ordtoplem.mm"
include "impbid.mm"

theorem ordtop
  let cJ: class J


  assert |- ( Ord J -> ( J e. Top <-> J =/= U. J ) )

  proof
    cJ
    word
    #
    cJ
    ctop
    wcel
    #
    cJ
    cJ
    cuni
    #
    wne
    #
    @1
    @2
    cJ
    wcel
    #
    @0
    @3
    cJ
    @2
    @2
    eqid
    topopn
    @0
    @4
    @3
    cJ
    @2
    nordeq
    ex
    syl5
    cJ
    ctop
    @2
    onsuctop
    ordtoplem
    impbid
end
