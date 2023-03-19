include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cfg.mm"
include "co.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "ssfg.mm"
include "adantr.mm"
include "sseld.mm"
include "ssel2.mm"
include "wi.mm"
include "elfg.mm"
include "simpr.mm"
include "syl6bi.mm"
include "adantl.mm"
include "syl5.mm"
include "expd.mm"
include "syl5d.mm"
include "ralrimdv.mm"
include "weq.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "sstr.mm"
include "sseq1.mm"
include "rspcev.mm"
include "a1d.mm"
include "sylanr2.mm"
include "ancld.mm"
include "exp45.mm"
include "rexlimdv.mm"
include "syld.mm"
include "impancom.mm"
include "com23.mm"
include "impd.mm"
include "wb.mm"
include "3imtr4d.mm"
include "ssrdv.mm"
include "ex.mm"
include "impbid.mm"

theorem fgss2
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cX: class X
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint X x
  disjoint X y
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint F t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint F u
  disjoint v x
  disjoint v y
  disjoint F v
  disjoint G t
  disjoint G u
  disjoint G v
  disjoint X t
  disjoint X u
  disjoint X v
  assert |- ( ( F e. ( fBas ` X ) /\ G e. ( fBas ` X ) ) -> ( ( X filGen F ) C_ ( X filGen G ) <-> A. x e. F E. y e. G y C_ x ) )

  proof
    cF
    cX
    cfbas
    cfv
    #
    wcel
    #
    cG
    @0
    wcel
    #
    wa
    #
    cX
    cF
    cfg
    co
    #
    cX
    cG
    cfg
    co
    #
    wss
    #
    vy
    cv
    #
    vx
    cv
    #
    wss
    #
    vy
    cG
    wrex
    #
    vx
    cF
    wral
    #
    @3
    @6
    @10
    vx
    cF
    @3
    @8
    cF
    wcel
    @8
    @4
    wcel
    #
    @6
    @10
    @3
    cF
    @4
    @8
    @1
    cF
    @4
    wss
    @2
    cF
    cX
    ssfg
    adantr
    sseld
    @3
    @6
    @12
    @10
    @6
    @12
    wa
    @8
    @5
    wcel
    #
    @3
    @10
    @4
    @5
    @8
    ssel2
    @2
    @13
    @10
    wi
    @1
    @2
    @13
    @8
    cX
    wss
    #
    @10
    wa
    @10
    vy
    @8
    cG
    cX
    elfg
    @14
    @10
    simpr
    syl6bi
    adantl
    syl5
    expd
    syl5d
    ralrimdv
    @3
    @11
    @6
    @3
    @11
    wa
    #
    vt
    @4
    @5
    @15
    vt
    cv
    #
    cX
    wss
    #
    vu
    cv
    #
    @16
    wss
    #
    vu
    cF
    wrex
    #
    wa
    #
    @17
    vv
    cv
    #
    @16
    wss
    #
    vv
    cG
    wrex
    #
    wa
    #
    @16
    @4
    wcel
    #
    @16
    @5
    wcel
    #
    @15
    @17
    @20
    @25
    @15
    @20
    @17
    @25
    @15
    @19
    @17
    @25
    wi
    #
    vu
    cF
    @3
    @18
    cF
    wcel
    #
    @11
    @19
    @28
    wi
    #
    @3
    @29
    wa
    #
    @11
    @7
    @18
    wss
    #
    vy
    cG
    wrex
    #
    @30
    @29
    @11
    @33
    wi
    @3
    @10
    @33
    vx
    @18
    cF
    vx
    vu
    weq
    @9
    @32
    vy
    cG
    @8
    @18
    @7
    sseq2
    rexbidv
    rspcv
    adantl
    @31
    @32
    @30
    vy
    cG
    @31
    @7
    cG
    wcel
    #
    @32
    @19
    @28
    @31
    @34
    @32
    @19
    wa
    #
    wa
    wa
    @17
    @24
    @35
    @31
    @34
    @7
    @16
    wss
    #
    @17
    @24
    wi
    @7
    @18
    @16
    sstr
    @31
    @34
    @36
    wa
    #
    wa
    @24
    @17
    @37
    @24
    @31
    @23
    @36
    vv
    @7
    cG
    @22
    @7
    @16
    sseq1
    rspcev
    adantl
    a1d
    sylanr2
    ancld
    exp45
    rexlimdv
    syld
    impancom
    rexlimdv
    com23
    impd
    @3
    @26
    @21
    wb
    #
    @11
    @1
    @38
    @2
    vu
    @16
    cF
    cX
    elfg
    adantr
    adantr
    @3
    @27
    @25
    wb
    #
    @11
    @2
    @39
    @1
    vv
    @16
    cG
    cX
    elfg
    adantl
    adantr
    3imtr4d
    ssrdv
    ex
    impbid
end
