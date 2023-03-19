include "con0.mm"
include "cep.mm"
include "wfr.mm"
include "cv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "dfepfr.mm"
include "wel.mm"
include "wex.mm"
include "n0.mm"
include "ineq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "adantll.mm"
include "inss1.mm"
include "wcel.mm"
include "word.mm"
include "ssel2.mm"
include "eloni.mm"
include "ordfr.mm"
include "3syl.mm"
include "inss2.mm"
include "vex.mm"
include "inex1.mm"
include "epfrc.mm"
include "mp3an2.mm"
include "sylan.mm"
include "wb.mm"
include "inass.mm"
include "syl.mm"
include "elinel2.mm"
include "ordelss.mm"
include "syl2an.mm"
include "sseqin2.mm"
include "sylib.mm"
include "ineq2d.mm"
include "syl5eq.mm"
include "rexbidva.mm"
include "adantr.mm"
include "mpbid.mm"
include "ssrexv.mm"
include "mpsyl.mm"
include "pm2.61dane.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "imp.mm"
include "mpgbir.mm"

theorem onfr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- _E Fr On

  proof
    con0
    cep
    wfr
    vx
    cv
    #
    con0
    wss
    #
    @0
    c0
    wne
    #
    wa
    @0
    vz
    cv
    #
    cin
    #
    c0
    wceq
    #
    vz
    @0
    wrex
    #
    wi
    vx
    vx
    vz
    con0
    dfepfr
    @1
    @2
    @6
    @2
    vy
    vx
    wel
    #
    vy
    wex
    @1
    @6
    vy
    @0
    n0
    @1
    @7
    @6
    vy
    @1
    @7
    @6
    @1
    @7
    wa
    #
    @6
    @0
    vy
    cv
    #
    cin
    #
    c0
    @7
    @10
    c0
    wceq
    #
    @6
    @1
    @5
    @11
    vz
    @9
    @0
    @3
    @9
    wceq
    @4
    @10
    c0
    @3
    @9
    @0
    ineq2
    eqeq1d
    rspcev
    adantll
    @10
    @0
    wss
    @8
    @10
    c0
    wne
    #
    wa
    #
    @5
    vz
    @10
    wrex
    #
    @6
    @0
    @9
    inss1
    @13
    @10
    @3
    cin
    #
    c0
    wceq
    #
    vz
    @10
    wrex
    #
    @14
    @8
    @9
    cep
    wfr
    #
    @12
    @17
    @8
    @9
    con0
    wcel
    #
    @9
    word
    #
    @18
    @0
    con0
    @9
    ssel2
    #
    @9
    eloni
    #
    @9
    ordfr
    3syl
    @18
    @10
    @9
    wss
    @12
    @17
    @0
    @9
    inss2
    vz
    @9
    @10
    @0
    @9
    vx
    vex
    inex1
    epfrc
    mp3an2
    sylan
    @8
    @17
    @14
    wb
    @12
    @8
    @16
    @5
    vz
    @10
    @8
    @3
    @10
    wcel
    #
    wa
    #
    @15
    @4
    c0
    @24
    @15
    @0
    @9
    @3
    cin
    #
    cin
    @4
    @0
    @9
    @3
    inass
    @24
    @25
    @3
    @0
    @24
    @3
    @9
    wss
    #
    @25
    @3
    wceq
    @8
    @20
    vz
    vy
    wel
    @26
    @23
    @8
    @19
    @20
    @21
    @22
    syl
    @3
    @0
    @9
    elinel2
    @9
    @3
    ordelss
    syl2an
    @3
    @9
    sseqin2
    sylib
    ineq2d
    syl5eq
    eqeq1d
    rexbidva
    adantr
    mpbid
    @5
    vz
    @10
    @0
    ssrexv
    mpsyl
    pm2.61dane
    ex
    exlimdv
    syl5bi
    imp
    mpgbir
end
