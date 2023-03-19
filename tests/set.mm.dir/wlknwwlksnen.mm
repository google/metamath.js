include "cuspgr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "cwlks.mm"
include "crab.mm"
include "cwwlksn.mm"
include "co.mm"
include "wf1o.mm"
include "wex.mm"
include "cen.mm"
include "wbr.mm"
include "wlknwwlksnbij2.mm"
include "bren.mm"
include "sylibr.mm"

theorem wlknwwlksnen
  let cG: class G
  let cN: class N
  let vp: setvar p
  let vf: setvar f

  disjoint G p
  disjoint N p
  disjoint G f
  disjoint f p
  disjoint N f
  assert |- ( ( G e. USPGraph /\ N e. NN0 ) -> { p e. ( Walks ` G ) | ( # ` ( 1st ` p ) ) = N } ~~ ( N WWalksN G ) )

  proof
    cG
    cuspgr
    wcel
    cN
    cn0
    wcel
    wa
    vp
    cv
    c1st
    cfv
    chash
    cfv
    cN
    wceq
    vp
    cG
    cwlks
    cfv
    crab
    #
    cN
    cG
    cwwlksn
    co
    #
    vf
    cv
    wf1o
    vf
    wex
    @0
    @1
    cen
    wbr
    vf
    cG
    cN
    vp
    wlknwwlksnbij2
    @0
    @1
    vf
    bren
    sylibr
end
