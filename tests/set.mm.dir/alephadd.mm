include "con0.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "ccda.mm"
include "co.mm"
include "cun.mm"
include "cen.mm"
include "wbr.mm"
include "wn.mm"
include "cvv.mm"
include "wa.mm"
include "wceq.mm"
include "ovex.mm"
include "cdm.mm"
include "wfn.mm"
include "alephfnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "notbii.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "c1o.mm"
include "0ex.mm"
include "cdaval.mm"
include "mp2an.mm"
include "xpundi.mm"
include "0xp.mm"
include "3eqtr2i.mm"
include "ndmfv.mm"
include "oveqan12d.mm"
include "adantr.mm"
include "adantl.mm"
include "uneq12d.mm"
include "un0.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "syl2anbr.mm"
include "eqeng.mm"
include "mpsyl.mm"
include "ex.mm"
include "com.mm"
include "wss.mm"
include "alephgeom.mm"
include "cdom.mm"
include "wi.mm"
include "fvex.mm"
include "ssdomg.mm"
include "ccrd.mm"
include "alephon.mm"
include "onenon.mm"
include "infcda.mm"
include "mp3an12.mm"
include "syl.mm"
include "sylbi.mm"
include "cdacomen.mm"
include "entr.mm"
include "sylancr.mm"
include "uncom.mm"
include "syl6breq.mm"
include "pm2.61ii.mm"

theorem alephadd
  let cA: class A
  let cB: class B


  assert |- ( ( aleph ` A ) +c ( aleph ` B ) ) ~~ ( ( aleph ` A ) u. ( aleph ` B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cA
    cale
    cfv
    #
    cB
    cale
    cfv
    #
    ccda
    co
    #
    @2
    @3
    cun
    #
    cen
    wbr
    #
    @0
    wn
    #
    @1
    wn
    #
    @6
    @4
    cvv
    wcel
    @7
    @8
    wa
    @4
    @5
    wceq
    #
    @6
    @2
    @3
    ccda
    ovex
    @7
    cA
    cale
    cdm
    #
    wcel
    #
    wn
    #
    cB
    @10
    wcel
    #
    wn
    #
    @9
    @8
    @11
    @0
    @10
    con0
    cA
    cale
    con0
    wfn
    @10
    con0
    wceq
    alephfnon
    con0
    cale
    fndm
    ax-mp
    #
    eleq2i
    notbii
    @13
    @1
    @10
    con0
    cB
    @15
    eleq2i
    notbii
    @12
    @14
    wa
    #
    c0
    c0
    ccda
    co
    #
    c0
    @4
    @5
    @17
    c0
    c0
    csn
    #
    cxp
    c0
    c1o
    csn
    #
    cxp
    cun
    #
    c0
    @18
    @19
    cun
    #
    cxp
    c0
    c0
    cvv
    wcel
    #
    @22
    @17
    @20
    wceq
    0ex
    0ex
    c0
    c0
    cvv
    cvv
    cdaval
    mp2an
    c0
    @18
    @19
    xpundi
    @21
    0xp
    3eqtr2i
    @12
    @14
    @2
    c0
    @3
    c0
    ccda
    cA
    cale
    ndmfv
    #
    cB
    cale
    ndmfv
    #
    oveqan12d
    @16
    @5
    c0
    c0
    cun
    c0
    @16
    @2
    c0
    @3
    c0
    @12
    @2
    c0
    wceq
    @14
    @23
    adantr
    @14
    @3
    c0
    wceq
    @12
    @24
    adantl
    uneq12d
    c0
    un0
    syl6eq
    3eqtr4a
    syl2anbr
    @4
    @5
    cvv
    eqeng
    mpsyl
    ex
    @0
    com
    @2
    wss
    #
    @6
    cA
    alephgeom
    @25
    com
    @2
    cdom
    wbr
    #
    @6
    @2
    cvv
    wcel
    @25
    @26
    wi
    cA
    cale
    fvex
    com
    @2
    cvv
    ssdomg
    ax-mp
    @2
    ccrd
    cdm
    #
    wcel
    #
    @3
    @27
    wcel
    #
    @26
    @6
    @2
    con0
    wcel
    @28
    cA
    alephon
    @2
    onenon
    ax-mp
    #
    @3
    con0
    wcel
    @29
    cB
    alephon
    @3
    onenon
    ax-mp
    #
    @2
    @3
    infcda
    mp3an12
    syl
    sylbi
    @1
    com
    @3
    wss
    #
    @6
    cB
    alephgeom
    @32
    com
    @3
    cdom
    wbr
    #
    @6
    @3
    cvv
    wcel
    @32
    @33
    wi
    cB
    cale
    fvex
    com
    @3
    cvv
    ssdomg
    ax-mp
    @33
    @4
    @3
    @2
    cun
    #
    @5
    cen
    @33
    @4
    @3
    @2
    ccda
    co
    #
    cen
    wbr
    @35
    @34
    cen
    wbr
    #
    @4
    @34
    cen
    wbr
    @2
    @3
    cdacomen
    @29
    @28
    @33
    @36
    @31
    @30
    @3
    @2
    infcda
    mp3an12
    @4
    @35
    @34
    entr
    sylancr
    @3
    @2
    uncom
    syl6breq
    syl
    sylbi
    pm2.61ii
end
