include "com.mm"
include "wcel.mm"
include "con0.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wreu.mm"
include "cvv.mm"
include "ssexg.mm"
include "ex.mm"
include "omelon2.mm"
include "syl6com.mm"
include "imp.mm"
include "adantll.mm"
include "simplr.mm"
include "jca.mm"
include "oawordeu.mm"
include "sylancom.mm"
include "reurex.mm"
include "syl.mm"
include "nnon.mm"
include "ad3antrrr.mm"
include "adantr.mm"
include "simpr.mm"
include "oaass.mm"
include "syl3anc.mm"
include "simpll.mm"
include "oaabslem.mm"
include "syl2anc.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "oveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "mpd.mm"

theorem oaabs
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C


  assert |- ( ( ( A e. _om /\ B e. On ) /\ _om C_ B ) -> ( A +o B ) = B )

  proof
    cA
    com
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    com
    cB
    wss
    #
    wa
    #
    com
    vx
    cv
    #
    coa
    co
    #
    cB
    wceq
    #
    vx
    con0
    wrex
    #
    cA
    cB
    coa
    co
    #
    cB
    wceq
    #
    @4
    @7
    vx
    con0
    wreu
    #
    @8
    @2
    @3
    com
    con0
    wcel
    #
    @1
    wa
    @11
    @4
    @12
    @1
    @1
    @3
    @12
    @0
    @1
    @3
    @12
    @3
    @1
    com
    cvv
    wcel
    #
    @12
    @3
    @1
    @13
    com
    cB
    con0
    ssexg
    ex
    omelon2
    syl6com
    imp
    adantll
    #
    @0
    @1
    @3
    simplr
    jca
    vx
    com
    cB
    oawordeu
    sylancom
    @7
    vx
    con0
    reurex
    syl
    @4
    @7
    @10
    vx
    con0
    @4
    @5
    con0
    wcel
    #
    wa
    #
    cA
    @6
    coa
    co
    #
    @6
    wceq
    @7
    @10
    @16
    cA
    com
    coa
    co
    #
    @5
    coa
    co
    #
    @17
    @6
    @16
    cA
    con0
    wcel
    #
    @12
    @15
    @19
    @17
    wceq
    @0
    @20
    @1
    @3
    @15
    cA
    nnon
    ad3antrrr
    @4
    @12
    @15
    @14
    adantr
    @4
    @15
    simpr
    cA
    com
    @5
    oaass
    syl3anc
    @16
    @18
    com
    @5
    coa
    @4
    @18
    com
    wceq
    #
    @15
    @4
    @12
    @0
    @21
    @14
    @0
    @1
    @3
    simpll
    cA
    oaabslem
    syl2anc
    adantr
    oveq1d
    eqtr3d
    @7
    @17
    @9
    @6
    cB
    @6
    cB
    cA
    coa
    oveq2
    @7
    id
    eqeq12d
    syl5ibcom
    rexlimdva
    mpd
end
