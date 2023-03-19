include "cfusgr.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cwwlksn.mm"
include "co.mm"
include "cfn.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "chash.mm"
include "wceq.mm"
include "cwlks.mm"
include "crab.mm"
include "cen.mm"
include "wbr.mm"
include "cvtx.mm"
include "eqid.mm"
include "fusgrvtxfi.mm"
include "adantr.mm"
include "wwlksnfi.mm"
include "syl.mm"
include "cuspgr.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "usgruspgr.mm"
include "wlknwwlksnen.mm"
include "sylan.mm"
include "enfii.mm"
include "syl2anc.mm"

theorem wlksnfi
  let cG: class G
  let cN: class N
  let vp: setvar p

  disjoint G p
  disjoint N p
  assert |- ( ( G e. FinUSGraph /\ N e. NN0 ) -> { p e. ( Walks ` G ) | ( # ` ( 1st ` p ) ) = N } e. Fin )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cN
    cG
    cwwlksn
    co
    #
    cfn
    wcel
    #
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
    @3
    cen
    wbr
    #
    @5
    cfn
    wcel
    @2
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    @4
    @0
    @8
    @1
    cG
    @7
    @7
    eqid
    fusgrvtxfi
    adantr
    cG
    cN
    wwlksnfi
    syl
    @0
    cG
    cuspgr
    wcel
    #
    @1
    @6
    @0
    cG
    cusgr
    wcel
    @9
    cG
    fusgrusgr
    cG
    usgruspgr
    syl
    cG
    cN
    vp
    wlknwwlksnen
    sylan
    @5
    @3
    enfii
    syl2anc
end
