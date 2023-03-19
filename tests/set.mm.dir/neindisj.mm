include "ctop.mm"
include "wcel.mm"
include "wss.mm"
include "ccl.mm"
include "cfv.mm"
include "csn.mm"
include "cnei.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "wa.mm"
include "cv.mm"
include "wrex.mm"
include "wb.mm"
include "clsss3.mm"
include "sseld.mm"
include "impr.mm"
include "isneip.mm"
include "syldan.mm"
include "w3a.mm"
include "3anass.mm"
include "clsndisj.mm"
include "sylanbr.mm"
include "anassrs.mm"
include "adantllr.mm"
include "adantrr.mm"
include "wceq.mm"
include "ssdisj.mm"
include "ex.mm"
include "necon3d.mm"
include "ad2antll.mm"
include "mpd.mm"
include "rexlimdva.mm"
include "expimpd.mm"
include "sylbid.mm"
include "exp32.mm"
include "imp43.mm"

theorem neindisj
  let cP: class P
  let cS: class S
  let cJ: class J
  let cN: class N
  let cX: class X
  let vg: setvar g
  let vh: setvar h
  let vp: setvar p
  let vv: setvar v
  let cM: class M
  assume neips.1: |- X = U. J


  assert |- ( ( ( J e. Top /\ S C_ X ) /\ ( P e. ( ( cls ` J ) ` S ) /\ N e. ( ( nei ` J ) ` { P } ) ) ) -> ( N i^i S ) =/= (/) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    cX
    wss
    #
    cP
    cS
    cJ
    ccl
    cfv
    cfv
    #
    wcel
    #
    cN
    cP
    csn
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    cN
    cS
    cin
    #
    c0
    wne
    #
    @0
    @1
    @3
    @4
    @6
    wi
    @0
    @1
    @3
    wa
    #
    wa
    #
    @4
    cN
    cX
    wss
    #
    cP
    vg
    cv
    #
    wcel
    #
    @10
    cN
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    wa
    #
    @6
    @0
    @7
    cP
    cX
    wcel
    #
    @4
    @15
    wb
    @0
    @1
    @3
    @16
    @0
    @1
    wa
    @2
    cX
    cP
    cS
    cJ
    cX
    neips.1
    clsss3
    sseld
    impr
    cP
    vg
    cJ
    cN
    cX
    neips.1
    isneip
    syldan
    @8
    @9
    @14
    @6
    @8
    @9
    wa
    #
    @13
    @6
    vg
    cJ
    @17
    @10
    cJ
    wcel
    #
    wa
    #
    @13
    @6
    @19
    @13
    wa
    @10
    cS
    cin
    #
    c0
    wne
    #
    @6
    @19
    @11
    @21
    @12
    @8
    @18
    @11
    @21
    @9
    @8
    @18
    @11
    @21
    @8
    @0
    @1
    @3
    w3a
    @18
    @11
    wa
    @21
    @0
    @1
    @3
    3anass
    cP
    cS
    @10
    cJ
    cX
    neips.1
    clsndisj
    sylanbr
    anassrs
    adantllr
    adantrr
    @12
    @21
    @6
    wi
    @19
    @11
    @12
    @5
    c0
    @20
    c0
    @12
    @5
    c0
    wceq
    @20
    c0
    wceq
    @10
    cN
    cS
    ssdisj
    ex
    necon3d
    ad2antll
    mpd
    ex
    rexlimdva
    expimpd
    sylbid
    exp32
    imp43
end
