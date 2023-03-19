include "cupgr.mm"
include "wcel.mm"
include "cv.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "cwwlks.mm"
include "wlkiswwlks1.mm"
include "exlimdv.mm"
include "wlkiswwlksupgr2.mm"
include "impbid.mm"

theorem wlkiswwlkupgr
  let cP: class P
  let vf: setvar f
  let cG: class G

  disjoint G f
  disjoint P f
  assert |- ( G e. UPGraph -> ( E. f f ( Walks ` G ) P <-> P e. ( WWalks ` G ) ) )

  proof
    cG
    cupgr
    wcel
    #
    vf
    cv
    #
    cP
    cG
    cwlks
    cfv
    wbr
    #
    vf
    wex
    cP
    cG
    cwwlks
    cfv
    wcel
    #
    @0
    @2
    @3
    vf
    cP
    @1
    cG
    wlkiswwlks1
    exlimdv
    cP
    vf
    cG
    wlkiswwlksupgr2
    impbid
end
