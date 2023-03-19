include "com.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "wrex.mm"
include "cfn.mm"
include "wpss.mm"
include "wceq.mm"
include "wo.mm"
include "sspss.mm"
include "pssnn.mm"
include "wi.mm"
include "elnn.mm"
include "expcom.mm"
include "anim1d.mm"
include "reximdv2.mm"
include "adantr.mm"
include "mpd.mm"
include "eleq1.mm"
include "biimparc.mm"
include "enrefg.mm"
include "ancli.mm"
include "breq2.mm"
include "rspcev.mm"
include "3syl.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "isfi.mm"
include "sylibr.mm"

theorem ssnnfi
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A e. _om /\ B C_ A ) -> B e. Fin )

  proof
    cA
    com
    wcel
    #
    cB
    cA
    wss
    #
    wa
    cB
    vx
    cv
    #
    cen
    wbr
    #
    vx
    com
    wrex
    #
    cB
    cfn
    wcel
    @1
    @0
    cB
    cA
    wpss
    #
    cB
    cA
    wceq
    #
    wo
    @4
    cB
    cA
    sspss
    @0
    @5
    @4
    @6
    @0
    @5
    wa
    @3
    vx
    cA
    wrex
    #
    @4
    vx
    cA
    cB
    pssnn
    @0
    @7
    @4
    wi
    @5
    @0
    @3
    @3
    vx
    cA
    com
    @0
    @2
    cA
    wcel
    #
    @2
    com
    wcel
    #
    @3
    @8
    @0
    @9
    @2
    cA
    elnn
    expcom
    anim1d
    reximdv2
    adantr
    mpd
    @0
    @6
    wa
    cB
    com
    wcel
    #
    @10
    cB
    cB
    cen
    wbr
    #
    wa
    @4
    @6
    @10
    @0
    cB
    cA
    com
    eleq1
    biimparc
    @10
    @11
    cB
    com
    enrefg
    ancli
    @3
    @11
    vx
    cB
    com
    @2
    cB
    cB
    cen
    breq2
    rspcev
    3syl
    jaodan
    sylan2b
    vx
    cB
    isfi
    sylibr
end
