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
include "cen.mm"
include "wbr.mm"
include "wlknwwlksnen.mm"
include "hasheni.mm"
include "syl.mm"

theorem wlknwwlksneqs
  let cG: class G
  let cN: class N
  let vp: setvar p

  disjoint G p
  disjoint N p
  assert |- ( ( G e. USPGraph /\ N e. NN0 ) -> ( # ` { p e. ( Walks ` G ) | ( # ` ( 1st ` p ) ) = N } ) = ( # ` ( N WWalksN G ) ) )

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
    cen
    wbr
    @0
    chash
    cfv
    @1
    chash
    cfv
    wceq
    cG
    cN
    vp
    wlknwwlksnen
    @0
    @1
    hasheni
    syl
end
