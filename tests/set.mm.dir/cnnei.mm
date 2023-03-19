include "ctop.mm"
include "wcel.mm"
include "wf.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wrex.mm"
include "wral.mm"
include "wb.mm"
include "wa.mm"
include "ccnp.mm"
include "ctopon.mm"
include "toptopon.mm"
include "anbi12i.mm"
include "cncnp.mm"
include "baibd.mm"
include "sylanb.mm"
include "anbi1i.mm"
include "iscnp4.mm"
include "3expa.mm"
include "an32s.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "3impa.mm"

theorem cnnei
  let vw: setvar w
  let vv: setvar v
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vp: setvar p
  assume cnnei.x: |- X = U. J
  assume cnnei.y: |- Y = U. K

  disjoint p v
  disjoint p w
  disjoint F p
  disjoint v w
  disjoint F v
  disjoint F w
  disjoint J p
  disjoint J v
  disjoint J w
  disjoint K p
  disjoint K v
  disjoint K w
  disjoint X p
  disjoint X v
  disjoint X w
  disjoint Y p
  disjoint Y v
  disjoint Y w
  assert |- ( ( J e. Top /\ K e. Top /\ F : X --> Y ) -> ( F e. ( J Cn K ) <-> A. p e. X A. w e. ( ( nei ` K ) ` { ( F ` p ) } ) E. v e. ( ( nei ` J ) ` { p } ) ( F " v ) C_ w ) )

  proof
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cF
    vv
    cv
    cima
    vw
    cv
    wss
    vv
    vp
    cv
    #
    csn
    cJ
    cnei
    cfv
    cfv
    wrex
    vw
    @4
    cF
    cfv
    csn
    cK
    cnei
    cfv
    cfv
    wral
    #
    vp
    cX
    wral
    #
    wb
    @0
    @1
    wa
    #
    @2
    wa
    #
    @3
    cF
    @4
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    vp
    cX
    wral
    #
    @6
    @7
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cK
    cY
    ctopon
    cfv
    wcel
    #
    wa
    #
    @2
    @3
    @10
    wb
    @0
    @11
    @1
    @12
    cJ
    cX
    cnnei.x
    toptopon
    cK
    cY
    cnnei.y
    toptopon
    anbi12i
    #
    @13
    @3
    @2
    @10
    vp
    cF
    cJ
    cK
    cX
    cY
    cncnp
    baibd
    sylanb
    @8
    @9
    @5
    vp
    cX
    @8
    @13
    @2
    wa
    @4
    cX
    wcel
    #
    @9
    @5
    wb
    #
    @7
    @13
    @2
    @14
    anbi1i
    @13
    @15
    @2
    @16
    @13
    @15
    wa
    @9
    @2
    @5
    @11
    @12
    @15
    @9
    @2
    @5
    wa
    wb
    vv
    vw
    @4
    cF
    cJ
    cK
    cX
    cY
    iscnp4
    3expa
    baibd
    an32s
    sylanb
    ralbidva
    bitrd
    3impa
end
