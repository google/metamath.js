include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "ccrd.mm"
include "cdm.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "cxp.mm"
include "cun.mm"
include "cen.mm"
include "wss.mm"
include "alephgeom.mm"
include "cvv.mm"
include "wi.mm"
include "fvex.mm"
include "ssdomg.mm"
include "ax-mp.mm"
include "sylbi.mm"
include "alephon.mm"
include "onenon.mm"
include "jctil.mm"
include "infn0.mm"
include "syl.mm"
include "infxp.mm"
include "syl2an.mm"

theorem alephmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( ( aleph ` A ) X. ( aleph ` B ) ) ~~ ( ( aleph ` A ) u. ( aleph ` B ) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    cale
    cfv
    #
    ccrd
    cdm
    #
    wcel
    #
    com
    @1
    cdom
    wbr
    #
    wa
    cB
    cale
    cfv
    #
    @2
    wcel
    #
    @5
    c0
    wne
    #
    wa
    @1
    @5
    cxp
    @1
    @5
    cun
    cen
    wbr
    cB
    con0
    wcel
    #
    @0
    @4
    @3
    @0
    com
    @1
    wss
    #
    @4
    cA
    alephgeom
    @1
    cvv
    wcel
    @9
    @4
    wi
    cA
    cale
    fvex
    com
    @1
    cvv
    ssdomg
    ax-mp
    sylbi
    @1
    con0
    wcel
    @3
    cA
    alephon
    @1
    onenon
    ax-mp
    jctil
    @8
    @7
    @6
    @8
    com
    @5
    wss
    #
    @7
    cB
    alephgeom
    @10
    com
    @5
    cdom
    wbr
    #
    @7
    @5
    cvv
    wcel
    @10
    @11
    wi
    cB
    cale
    fvex
    com
    @5
    cvv
    ssdomg
    ax-mp
    @5
    infn0
    syl
    sylbi
    @5
    con0
    wcel
    @6
    cB
    alephon
    @5
    onenon
    ax-mp
    jctil
    @1
    @5
    infxp
    syl2an
end
