include "cuspgr.mm"
include "wcel.mm"
include "cwlks.mm"
include "cfv.mm"
include "cwwlks.mm"
include "cv.mm"
include "c2nd.mm"
include "cmpt.mm"
include "wf1o.mm"
include "wex.mm"
include "eqid.mm"
include "wlkpwwlkf1ouspgr.mm"
include "fvex.mm"
include "mptex.mm"
include "f1oeq1.mm"
include "spcev.mm"
include "syl.mm"

theorem wlkisowwlkupgr
  let vf: setvar f
  let cG: class G
  let vw: setvar w

  disjoint G f
  disjoint G w
  disjoint f w
  assert |- ( G e. USPGraph -> E. f f : ( Walks ` G ) -1-1-onto-> ( WWalks ` G ) )

  proof
    cG
    cuspgr
    wcel
    cG
    cwlks
    cfv
    #
    cG
    cwwlks
    cfv
    #
    vw
    @0
    vw
    cv
    c2nd
    cfv
    #
    cmpt
    #
    wf1o
    #
    @0
    @1
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    vw
    @3
    cG
    @3
    eqid
    wlkpwwlkf1ouspgr
    @6
    @4
    vf
    @3
    vw
    @0
    @2
    cG
    cwlks
    fvex
    mptex
    @0
    @1
    @5
    @3
    f1oeq1
    spcev
    syl
end
