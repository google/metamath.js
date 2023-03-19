include "wcel.mm"
include "cflim.mm"
include "co.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "csn.mm"
include "cnei.mm"
include "wral.mm"
include "cuni.mm"
include "cfil.mm"
include "eqid.mm"
include "flimfil.mm"
include "ad2antlr.mm"
include "flimnei.mm"
include "adantll.mm"
include "simpll.mm"
include "filinn0.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "ctop.mm"
include "wss.mm"
include "wb.mm"
include "flimtop.mm"
include "adantl.mm"
include "filelss.mm"
include "ancoms.mm"
include "sylan2.mm"
include "flimelbas.mm"
include "neindisj2.mm"
include "mpbird.mm"
include "ex.mm"
include "ssrdv.mm"

theorem flimclsi
  let cS: class S
  let cF: class F
  let cJ: class J
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let cX: class X


  assert |- ( S e. F -> ( J fLim F ) C_ ( ( cls ` J ) ` S ) )

  proof
    cS
    cF
    wcel
    #
    vx
    cJ
    cF
    cflim
    co
    #
    cS
    cJ
    ccl
    cfv
    cfv
    #
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    @4
    wa
    #
    @5
    vy
    cv
    #
    cS
    cin
    c0
    wne
    #
    vy
    @3
    csn
    cJ
    cnei
    cfv
    cfv
    #
    wral
    #
    @6
    @8
    vy
    @9
    @6
    @7
    @9
    wcel
    #
    wa
    cF
    cJ
    cuni
    #
    cfil
    cfv
    wcel
    #
    @7
    cF
    wcel
    #
    @0
    @8
    @4
    @13
    @0
    @11
    @3
    cF
    cJ
    @12
    @12
    eqid
    #
    flimfil
    #
    ad2antlr
    @4
    @11
    @14
    @0
    @3
    cF
    cJ
    @7
    flimnei
    adantll
    @0
    @4
    @11
    simpll
    @7
    cS
    cF
    @12
    filinn0
    syl3anc
    ralrimiva
    @6
    cJ
    ctop
    wcel
    #
    cS
    @12
    wss
    #
    @3
    @12
    wcel
    #
    @5
    @10
    wb
    @4
    @17
    @0
    @3
    cF
    cJ
    flimtop
    adantl
    @4
    @0
    @13
    @18
    @16
    @13
    @0
    @18
    cS
    cF
    @12
    filelss
    ancoms
    sylan2
    @4
    @19
    @0
    @3
    cF
    cJ
    @12
    @15
    flimelbas
    adantl
    @3
    cS
    vy
    cJ
    @12
    @15
    neindisj2
    syl3anc
    mpbird
    ex
    ssrdv
end
