include "word.mm"
include "ctop.mm"
include "wcel.mm"
include "cconn.mm"
include "cuni.mm"
include "wne.mm"
include "ordtop.mm"
include "onsucconn.mm"
include "ordtoplem.mm"
include "sylbid.mm"
include "conntop.mm"
include "impbid1.mm"

theorem ordtopconn
  let cJ: class J


  assert |- ( Ord J -> ( J e. Top <-> J e. Conn ) )

  proof
    cJ
    word
    #
    cJ
    ctop
    wcel
    #
    cJ
    cconn
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
    cconn
    @3
    onsucconn
    ordtoplem
    sylbid
    cJ
    conntop
    impbid1
end
