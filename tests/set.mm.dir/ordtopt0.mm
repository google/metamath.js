include "word.mm"
include "ctop.mm"
include "wcel.mm"
include "ct0.mm"
include "cuni.mm"
include "wne.mm"
include "ordtop.mm"
include "onsuct0.mm"
include "ordtoplem.mm"
include "sylbid.mm"
include "t0top.mm"
include "impbid1.mm"

theorem ordtopt0
  let cJ: class J


  assert |- ( Ord J -> ( J e. Top <-> J e. Kol2 ) )

  proof
    cJ
    word
    #
    cJ
    ctop
    wcel
    #
    cJ
    ct0
    wcel
    #
    @0
    @1
    cJ
    cJ
    cuni
    #
    wne
    @2
    cJ
    ordtop
    cJ
    ct0
    @3
    onsuct0
    ordtoplem
    sylbid
    cJ
    t0top
    impbid1
end
