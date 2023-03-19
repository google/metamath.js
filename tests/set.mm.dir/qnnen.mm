include "cq.mm"
include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "cen.mm"
include "cz.mm"
include "cxp.mm"
include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt2.mm"
include "wfo.mm"
include "com.mm"
include "con0.mm"
include "omelon.mm"
include "nnenom.mm"
include "ensymi.mm"
include "isnumi.mm"
include "mp2an.mm"
include "wb.mm"
include "znnen.mm"
include "ennum.mm"
include "ax-mp.mm"
include "mpbir.mm"
include "xpnum.mm"
include "wfn.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "ovex.mm"
include "fnmpt2i.mm"
include "wrex.mm"
include "cab.mm"
include "rnmpt2.mm"
include "elq.mm"
include "abbi2i.mm"
include "eqtr4i.mm"
include "df-fo.mm"
include "mpbir2an.mm"
include "fodomnum.mm"
include "mp2.mm"
include "nnex.mm"
include "enref.mm"
include "xpen.mm"
include "xpnnen.mm"
include "entri.mm"
include "domentr.mm"
include "cvv.mm"
include "wss.mm"
include "qex.mm"
include "nnssq.mm"
include "ssdomg.mm"
include "sbth.mm"

theorem qnnen
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- QQ ~~ NN

  proof
    cq
    cn
    cdom
    wbr
    #
    cn
    cq
    cdom
    wbr
    #
    cq
    cn
    cen
    wbr
    cq
    cz
    cn
    cxp
    #
    cdom
    wbr
    #
    @2
    cn
    cen
    wbr
    @0
    @2
    ccrd
    cdm
    #
    wcel
    #
    @2
    cq
    vx
    vy
    cz
    cn
    vx
    cv
    #
    vy
    cv
    #
    cdiv
    co
    #
    cmpt2
    #
    wfo
    #
    @3
    cz
    @4
    wcel
    #
    cn
    @4
    wcel
    #
    @5
    @11
    @12
    com
    con0
    wcel
    com
    cn
    cen
    wbr
    @12
    omelon
    cn
    com
    nnenom
    ensymi
    com
    cn
    isnumi
    mp2an
    #
    cz
    cn
    cen
    wbr
    #
    @11
    @12
    wb
    znnen
    cz
    cn
    ennum
    ax-mp
    mpbir
    @13
    cz
    cn
    xpnum
    mp2an
    @10
    @9
    @2
    wfn
    @9
    crn
    #
    cq
    wceq
    vx
    vy
    cz
    cn
    @8
    @9
    @9
    eqid
    #
    @6
    @7
    cdiv
    ovex
    fnmpt2i
    @15
    vz
    cv
    #
    @8
    wceq
    vy
    cn
    wrex
    vx
    cz
    wrex
    #
    vz
    cab
    cq
    vx
    vy
    vz
    cz
    cn
    @8
    @9
    @16
    rnmpt2
    @18
    vz
    cq
    vx
    vy
    @17
    elq
    abbi2i
    eqtr4i
    @2
    cq
    @9
    df-fo
    mpbir2an
    @2
    cq
    @9
    fodomnum
    mp2
    @2
    cn
    cn
    cxp
    #
    cn
    @14
    cn
    cn
    cen
    wbr
    @2
    @19
    cen
    wbr
    znnen
    cn
    nnex
    enref
    cz
    cn
    cn
    cn
    xpen
    mp2an
    xpnnen
    entri
    cq
    @2
    cn
    domentr
    mp2an
    cq
    cvv
    wcel
    cn
    cq
    wss
    @1
    qex
    nnssq
    cn
    cq
    cvv
    ssdomg
    mp2
    cq
    cn
    sbth
    mp2an
end
