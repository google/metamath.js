include "wcel.mm"
include "cword.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "ciun.mm"
include "cvv.mm"
include "wrdval.mm"
include "cz.mm"
include "cxp.mm"
include "cpw.mm"
include "wss.mm"
include "wral.mm"
include "mapsspw.mm"
include "elfzoelz.mm"
include "ssriv.mm"
include "xpss1.mm"
include "ax-mp.mm"
include "sspwb.mm"
include "mpbi.mm"
include "sstri.mm"
include "rgenw.mm"
include "iunss.mm"
include "mpbir.mm"
include "zex.mm"
include "xpexg.mm"
include "mpan.mm"
include "pwexg.mm"
include "syl.mm"
include "ssexg.mm"
include "sylancr.mm"
include "eqeltrd.mm"

theorem wrdexg
  let cS: class S
  let cV: class V
  let vl: setvar l
  let vs: setvar s


  assert |- ( S e. V -> Word S e. _V )

  proof
    cS
    cV
    wcel
    #
    cS
    cword
    vl
    cn0
    cS
    cc0
    vl
    cv
    #
    cfzo
    co
    #
    cmap
    co
    #
    ciun
    #
    cvv
    cS
    cV
    vl
    wrdval
    @0
    @4
    cz
    cS
    cxp
    #
    cpw
    #
    wss
    #
    @6
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @7
    @3
    @6
    wss
    #
    vl
    cn0
    wral
    @9
    vl
    cn0
    @3
    @2
    cS
    cxp
    #
    cpw
    #
    @6
    cS
    @2
    mapsspw
    @10
    @5
    wss
    #
    @11
    @6
    wss
    @2
    cz
    wss
    @12
    vs
    @2
    cz
    vs
    cv
    cc0
    @1
    elfzoelz
    ssriv
    @2
    cz
    cS
    xpss1
    ax-mp
    @10
    @5
    sspwb
    mpbi
    sstri
    rgenw
    vl
    cn0
    @3
    @6
    iunss
    mpbir
    @0
    @5
    cvv
    wcel
    #
    @8
    cz
    cvv
    wcel
    @0
    @13
    zex
    cz
    cS
    cvv
    cV
    xpexg
    mpan
    @5
    cvv
    pwexg
    syl
    @4
    @6
    cvv
    ssexg
    sylancr
    eqeltrd
end
