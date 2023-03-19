include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cale.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "cen.mm"
include "wbr.mm"
include "c2o.mm"
include "ccrd.mm"
include "cdm.mm"
include "com.mm"
include "cdom.mm"
include "alephon.mm"
include "onenon.mm"
include "mp1i.mm"
include "cvv.mm"
include "fvex.mm"
include "simplr.mm"
include "alephgeom.mm"
include "sylib.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "word.mm"
include "ordom.mm"
include "2onn.mm"
include "ordelss.mm"
include "mp2an.mm"
include "simpll.mm"
include "syl5ss.mm"
include "alephord3.mm"
include "wi.mm"
include "ax-mp.mm"
include "syl6bi.mm"
include "imp.mm"
include "csdm.mm"
include "canth2.mm"
include "sdomdom.mm"
include "domtr.mm"
include "sylancl.mm"
include "mappwen.mm"
include "syl22anc.mm"
include "wb.mm"
include "pw2en.mm"
include "enen2.mm"

theorem alephexp1
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. On /\ B e. On ) /\ A C_ B ) -> ( ( aleph ` A ) ^m ( aleph ` B ) ) ~~ ( 2o ^m ( aleph ` B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    wa
    #
    cA
    cale
    cfv
    #
    cB
    cale
    cfv
    #
    cmap
    co
    #
    @6
    cpw
    #
    cen
    wbr
    #
    @7
    c2o
    @6
    cmap
    co
    #
    cen
    wbr
    #
    @4
    @6
    ccrd
    cdm
    wcel
    #
    com
    @6
    cdom
    wbr
    #
    c2o
    @5
    cdom
    wbr
    #
    @5
    @8
    cdom
    wbr
    #
    @9
    @6
    con0
    wcel
    @12
    @4
    cB
    alephon
    @6
    onenon
    mp1i
    @6
    cvv
    wcel
    #
    @4
    com
    @6
    wss
    #
    @13
    cB
    cale
    fvex
    #
    @4
    @1
    @17
    @0
    @1
    @3
    simplr
    cB
    alephgeom
    sylib
    com
    @6
    cvv
    ssdomg
    mpsyl
    @5
    cvv
    wcel
    @4
    c2o
    @5
    wss
    @14
    cA
    cale
    fvex
    @4
    c2o
    com
    @5
    com
    word
    c2o
    com
    wcel
    c2o
    com
    wss
    ordom
    2onn
    com
    c2o
    ordelss
    mp2an
    @4
    @0
    com
    @5
    wss
    @0
    @1
    @3
    simpll
    cA
    alephgeom
    sylib
    syl5ss
    c2o
    @5
    cvv
    ssdomg
    mpsyl
    @4
    @5
    @6
    cdom
    wbr
    #
    @6
    @8
    cdom
    wbr
    #
    @15
    @2
    @3
    @19
    @2
    @3
    @5
    @6
    wss
    #
    @19
    cA
    cB
    alephord3
    @16
    @21
    @19
    wi
    @18
    @5
    @6
    cvv
    ssdomg
    ax-mp
    syl6bi
    imp
    @6
    @8
    csdm
    wbr
    @20
    @6
    @18
    canth2
    @6
    @8
    sdomdom
    ax-mp
    @5
    @6
    @8
    domtr
    sylancl
    @5
    @6
    mappwen
    syl22anc
    @8
    @10
    cen
    wbr
    @9
    @11
    wb
    @6
    @18
    pw2en
    @8
    @10
    @7
    enen2
    ax-mp
    sylib
end
