include "cuspgr.mm"
include "wcel.mm"
include "cv.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "wex.mm"
include "cwwlks.mm"
include "cupgr.mm"
include "wi.mm"
include "uspgrupgr.mm"
include "wlkiswwlks1.mm"
include "syl.mm"
include "exlimdv.mm"
include "wlkiswwlks2.mm"
include "impbid.mm"

theorem wlkiswwlks
  let cP: class P
  let vf: setvar f
  let cG: class G

  disjoint G f
  disjoint P f
  assert |- ( G e. USPGraph -> ( E. f f ( Walks ` G ) P <-> P e. ( WWalks ` G ) ) )

  proof
    cG
    cuspgr
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
    @0
    cG
    cupgr
    wcel
    @2
    @3
    wi
    cG
    uspgrupgr
    cP
    @1
    cG
    wlkiswwlks1
    syl
    exlimdv
    cP
    vf
    cG
    wlkiswwlks2
    impbid
end
