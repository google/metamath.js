include "cwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "c1st.mm"
include "c2nd.mm"
include "wbr.mm"
include "cv.mm"
include "wex.mm"
include "wlkcpr.mm"
include "fvex.mm"
include "breq12.mm"
include "spc2ev.mm"
include "sylbi.mm"

theorem wlk2f
  let vf: setvar f
  let cG: class G
  let cW: class W
  let vp: setvar p

  disjoint G f
  disjoint G p
  disjoint f p
  disjoint W f
  disjoint W p
  assert |- ( W e. ( Walks ` G ) -> E. f E. p f ( Walks ` G ) p )

  proof
    cW
    cG
    cwlks
    cfv
    #
    wcel
    cW
    c1st
    cfv
    #
    cW
    c2nd
    cfv
    #
    @0
    wbr
    #
    vf
    cv
    #
    vp
    cv
    #
    @0
    wbr
    #
    vp
    wex
    vf
    wex
    cG
    cW
    wlkcpr
    @6
    @3
    vf
    vp
    @1
    @2
    cW
    c1st
    fvex
    cW
    c2nd
    fvex
    @4
    @1
    @5
    @2
    @0
    breq12
    spc2ev
    sylbi
end
