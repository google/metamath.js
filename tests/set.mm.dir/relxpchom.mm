include "co.mm"
include "wrel.mm"
include "cvv.mm"
include "cxp.mm"
include "wss.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "chom.mm"
include "c2nd.mm"
include "cbs.mm"
include "wral.mm"
include "xpss.mm"
include "rgen2w.mm"
include "eqid.mm"
include "xpchomfval.mm"
include "ovmptss.mm"
include "ax-mp.mm"
include "df-rel.mm"
include "mpbir.mm"

theorem relxpchom
  let cC: class C
  let cD: class D
  let cT: class T
  let cK: class K
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vv: setvar v
  assume relxpchom.t: |- T = ( C Xc. D )
  assume relxpchom.k: |- K = ( Hom ` T )


  assert |- Rel ( X K Y )

  proof
    cX
    cY
    cK
    co
    #
    wrel
    @0
    cvv
    cvv
    cxp
    #
    wss
    #
    vu
    cv
    #
    c1st
    cfv
    vv
    cv
    #
    c1st
    cfv
    cC
    chom
    cfv
    #
    co
    #
    @3
    c2nd
    cfv
    @4
    c2nd
    cfv
    cD
    chom
    cfv
    #
    co
    #
    cxp
    #
    @1
    wss
    #
    vv
    cT
    cbs
    cfv
    #
    wral
    vu
    @11
    wral
    @2
    @10
    vu
    vv
    @11
    @11
    @6
    @8
    xpss
    rgen2w
    vu
    vv
    @11
    @11
    @9
    cX
    cK
    cY
    @1
    vv
    vu
    @11
    cC
    cD
    cT
    @5
    @7
    cK
    relxpchom.t
    @11
    eqid
    @5
    eqid
    @7
    eqid
    relxpchom.k
    xpchomfval
    ovmptss
    ax-mp
    @0
    df-rel
    mpbir
end
