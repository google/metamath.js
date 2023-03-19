include "con0.mm"
include "wcel.mm"
include "c2o.mm"
include "cdom.mm"
include "wbr.mm"
include "cale.mm"
include "cfv.mm"
include "cmap.mm"
include "co.mm"
include "ccrd.mm"
include "ccf.mm"
include "csdm.mm"
include "wi.mm"
include "wa.mm"
include "cxp.mm"
include "cen.mm"
include "ovex.mm"
include "cardid.mm"
include "ensymi.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "com.mm"
include "wn.mm"
include "cpw.mm"
include "fvex.mm"
include "canth2.mm"
include "pw2en.mm"
include "sdomentr.mm"
include "mp2an.mm"
include "mapdom1.mm"
include "sdomdomtr.mm"
include "sylancr.mm"
include "cfn.mm"
include "cvv.mm"
include "wb.mm"
include "ficard.mm"
include "ax-mp.mm"
include "isfinite.mm"
include "sdomdom.mm"
include "sylbi.mm"
include "sylbir.mm"
include "wss.mm"
include "alephgeom.mm"
include "alephon.mm"
include "ssdomg.mm"
include "domtr.mm"
include "syl2an.mm"
include "domnsym.mm"
include "syl.mm"
include "expcom.mm"
include "con2d.mm"
include "cardidm.mm"
include "cun.mm"
include "wo.mm"
include "iscard3.mm"
include "elun.mm"
include "df-or.mm"
include "3bitri.mm"
include "mpbi.mm"
include "syl56.mm"
include "wfn.mm"
include "alephfnon.mm"
include "fvelrnb.mm"
include "syl6ib.mm"
include "char.mm"
include "cmpt.mm"
include "eqid.mm"
include "pwcfsdom.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "breq12d.mm"
include "mpbii.mm"
include "rexlimivw.mm"
include "syl6.mm"
include "imp.mm"
include "ensdomtr.mm"
include "enref.mm"
include "mapen.mm"
include "mapxpen.mm"
include "mp3an.mm"
include "entri.mm"
include "sylancl.mm"
include "c0.mm"
include "xpdom2.mm"
include "biimpi.mm"
include "infxpen.mm"
include "domentr.mm"
include "c1o.mm"
include "csuc.mm"
include "nsuceq0.mm"
include "dom0.mm"
include "nemtbir.mm"
include "df-2o.mm"
include "breq1i.mm"
include "breq2.mm"
include "syl5bb.mm"
include "biimpcd.mm"
include "adantld.mm"
include "mtoi.mm"
include "mapdom2.mm"
include "expl.mm"
include "com12.mm"
include "mt2d.mm"
include "domtri.mm"
include "biimpri.mm"
include "nsyl2.mm"
include "ex.mm"
include "cdm.mm"
include "fndm.mm"
include "eleq2i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "wne.mm"
include "1n0.mm"
include "1onn.mm"
include "elexi.mm"
include "0sdom.mm"
include "mpbir.mm"
include "oveq2.mm"
include "map0e.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "cardnn.mm"
include "df-1o.mm"
include "fveq2i.mm"
include "0elon.mm"
include "cfsuc.mm"
include "eqtri.mm"
include "mpbiri.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem cfpwsdom
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume cfpwsdom.1: |- B e. _V


  assert |- ( 2o ~<_ B -> ( aleph ` A ) ~< ( cf ` ( card ` ( B ^m ( aleph ` A ) ) ) ) )

  proof
    cA
    con0
    wcel
    #
    c2o
    cB
    cdom
    wbr
    #
    cA
    cale
    cfv
    #
    cB
    @2
    cmap
    co
    #
    ccrd
    cfv
    #
    ccf
    cfv
    #
    csdm
    wbr
    #
    wi
    #
    @0
    @1
    @6
    @0
    @1
    wa
    #
    @5
    @2
    cdom
    wbr
    #
    @6
    @8
    @9
    @3
    cB
    @2
    @5
    cxp
    #
    cmap
    co
    #
    csdm
    wbr
    #
    @8
    @3
    @4
    @5
    cmap
    co
    #
    csdm
    wbr
    #
    @13
    @11
    cen
    wbr
    @12
    @8
    @3
    @4
    cen
    wbr
    @4
    @13
    csdm
    wbr
    #
    @14
    @4
    @3
    @3
    cB
    @2
    cmap
    ovex
    #
    cardid
    #
    ensymi
    @0
    @1
    @15
    @0
    @1
    vx
    cv
    #
    cale
    cfv
    #
    @4
    wceq
    #
    vx
    con0
    wrex
    #
    @15
    @0
    @1
    @4
    cale
    crn
    #
    wcel
    #
    @21
    @1
    @2
    @3
    csdm
    wbr
    #
    @0
    @4
    com
    wcel
    #
    wn
    #
    @23
    @1
    @2
    c2o
    @2
    cmap
    co
    #
    csdm
    wbr
    #
    @27
    @3
    cdom
    wbr
    @24
    @2
    @2
    cpw
    #
    csdm
    wbr
    @29
    @27
    cen
    wbr
    @28
    @2
    cA
    cale
    fvex
    #
    canth2
    @2
    @30
    pw2en
    @2
    @29
    @27
    sdomentr
    mp2an
    c2o
    cB
    @2
    mapdom1
    @2
    @27
    @3
    sdomdomtr
    sylancr
    @0
    @25
    @24
    @25
    @0
    @24
    wn
    #
    @25
    @0
    wa
    @3
    @2
    cdom
    wbr
    #
    @31
    @25
    @3
    com
    cdom
    wbr
    #
    com
    @2
    cdom
    wbr
    #
    @32
    @0
    @25
    @3
    cfn
    wcel
    #
    @33
    @3
    cvv
    wcel
    @35
    @25
    wb
    @16
    @3
    cvv
    ficard
    ax-mp
    @35
    @3
    com
    csdm
    wbr
    @33
    @3
    isfinite
    @3
    com
    sdomdom
    sylbi
    sylbir
    @0
    com
    @2
    wss
    #
    @34
    cA
    alephgeom
    #
    @2
    con0
    wcel
    #
    @36
    @34
    wi
    cA
    alephon
    #
    com
    @2
    con0
    ssdomg
    ax-mp
    sylbi
    @3
    com
    @2
    domtr
    syl2an
    @3
    @2
    domnsym
    syl
    expcom
    con2d
    @4
    ccrd
    cfv
    @4
    wceq
    #
    @26
    @23
    wi
    #
    @3
    cardidm
    @40
    @4
    com
    @22
    cun
    wcel
    @25
    @23
    wo
    @41
    @4
    iscard3
    @4
    com
    @22
    elun
    @25
    @23
    df-or
    3bitri
    mpbi
    syl56
    cale
    con0
    wfn
    #
    @23
    @21
    wb
    alephfnon
    vx
    con0
    @4
    cale
    fvelrnb
    ax-mp
    syl6ib
    @20
    @15
    vx
    con0
    @20
    @19
    @19
    @19
    ccf
    cfv
    #
    cmap
    co
    #
    csdm
    wbr
    @15
    vy
    @18
    vz
    vy
    @43
    vy
    cv
    vz
    cv
    cfv
    char
    cfv
    cmpt
    #
    @45
    eqid
    pwcfsdom
    @20
    @19
    @4
    @44
    @13
    csdm
    @20
    id
    #
    @20
    @19
    @4
    @43
    @5
    cmap
    @46
    @19
    @4
    ccf
    fveq2
    oveq12d
    breq12d
    mpbii
    rexlimivw
    syl6
    imp
    @3
    @4
    @13
    ensdomtr
    sylancr
    @13
    @3
    @5
    cmap
    co
    #
    @11
    @4
    @3
    cen
    wbr
    @5
    @5
    cen
    wbr
    @13
    @47
    cen
    wbr
    @17
    @5
    @4
    ccf
    fvex
    #
    enref
    @4
    @3
    @5
    @5
    mapen
    mp2an
    cB
    cvv
    wcel
    #
    @38
    @5
    cvv
    wcel
    #
    @47
    @11
    cen
    wbr
    cfpwsdom.1
    @39
    @48
    cB
    @2
    @5
    cvv
    con0
    cvv
    mapxpen
    mp3an
    entri
    @3
    @13
    @11
    sdomentr
    sylancl
    @9
    @8
    @12
    wn
    #
    @9
    @0
    @1
    @51
    @9
    @0
    wa
    #
    @1
    wa
    @11
    @3
    cdom
    wbr
    #
    @51
    @52
    @10
    @2
    cdom
    wbr
    #
    @10
    c0
    wceq
    #
    cB
    c0
    wceq
    #
    wa
    #
    wn
    @53
    @1
    @9
    @10
    @2
    @2
    cxp
    #
    cdom
    wbr
    @58
    @2
    cen
    wbr
    #
    @54
    @0
    @5
    @2
    @2
    @30
    xpdom2
    @0
    @38
    @36
    @59
    @39
    @0
    @36
    @37
    biimpi
    @2
    infxpen
    sylancr
    @10
    @58
    @2
    domentr
    syl2an
    @1
    @57
    c1o
    csuc
    #
    c0
    cdom
    wbr
    #
    @61
    @60
    c0
    c1o
    nsuceq0
    @60
    dom0
    nemtbir
    @1
    @56
    @61
    @55
    @56
    @1
    @61
    @1
    @60
    cB
    cdom
    wbr
    @56
    @61
    c2o
    @60
    cB
    cdom
    df-2o
    breq1i
    cB
    c0
    @60
    cdom
    breq2
    syl5bb
    biimpcd
    adantld
    mtoi
    @10
    @2
    cB
    mapdom2
    syl2an
    @11
    @3
    domnsym
    syl
    expl
    com12
    mt2d
    @9
    @6
    wn
    #
    @50
    @2
    cvv
    wcel
    @9
    @62
    wb
    @48
    @30
    @5
    @2
    cvv
    cvv
    domtri
    mp2an
    biimpri
    nsyl2
    ex
    @0
    wn
    @2
    c0
    wceq
    #
    @7
    @0
    cA
    cale
    cdm
    #
    wcel
    @63
    @64
    con0
    cA
    @42
    @64
    con0
    wceq
    alephfnon
    con0
    cale
    fndm
    ax-mp
    eleq2i
    cA
    cale
    ndmfv
    sylnbir
    @63
    @6
    @1
    @63
    @6
    c0
    c1o
    csdm
    wbr
    #
    @65
    c1o
    c0
    wne
    1n0
    c1o
    c1o
    com
    1onn
    elexi
    0sdom
    mpbir
    @63
    @2
    c0
    @5
    c1o
    csdm
    @63
    id
    @63
    @5
    c1o
    ccf
    cfv
    #
    c1o
    @63
    @4
    c1o
    ccf
    @63
    @4
    c1o
    ccrd
    cfv
    #
    c1o
    @63
    @3
    c1o
    ccrd
    @63
    @3
    cB
    c0
    cmap
    co
    #
    c1o
    @2
    c0
    cB
    cmap
    oveq2
    @49
    @68
    c1o
    wceq
    cfpwsdom.1
    cB
    cvv
    map0e
    ax-mp
    syl6eq
    fveq2d
    c1o
    com
    wcel
    @67
    c1o
    wceq
    1onn
    c1o
    cardnn
    ax-mp
    syl6eq
    fveq2d
    @66
    c0
    csuc
    #
    ccf
    cfv
    #
    c1o
    c1o
    @69
    ccf
    df-1o
    fveq2i
    c0
    con0
    wcel
    @70
    c1o
    wceq
    0elon
    c0
    cfsuc
    ax-mp
    eqtri
    syl6eq
    breq12d
    mpbiri
    a1d
    syl
    pm2.61i
end
