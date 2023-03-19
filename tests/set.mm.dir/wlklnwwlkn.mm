include "cuspgr.mm"
include "wcel.mm"
include "cv.mm"
include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "cwwlksn.mm"
include "co.mm"
include "cupgr.mm"
include "wi.mm"
include "uspgrupgr.mm"
include "wlklnwwlkln1.mm"
include "syl.mm"
include "exlimdv.mm"
include "wlklnwwlkln2.mm"
include "impbid.mm"

theorem wlklnwwlkn
  let cP: class P
  let vf: setvar f
  let cG: class G
  let cN: class N

  disjoint G f
  disjoint N f
  disjoint P f
  assert |- ( G e. USPGraph -> ( E. f ( f ( Walks ` G ) P /\ ( # ` f ) = N ) <-> P e. ( N WWalksN G ) ) )

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
    @1
    chash
    cfv
    cN
    wceq
    wa
    #
    vf
    wex
    cP
    cN
    cG
    cwwlksn
    co
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
    cN
    wlklnwwlkln1
    syl
    exlimdv
    cP
    vf
    cG
    cN
    wlklnwwlkln2
    impbid
end
