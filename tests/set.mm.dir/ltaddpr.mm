include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cpp.mm"
include "co.mm"
include "cltp.mm"
include "wbr.mm"
include "wpss.mm"
include "cv.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "prn0.mm"
include "n0.mm"
include "sylib.mm"
include "adantl.mm"
include "wss.mm"
include "wceq.mm"
include "wn.mm"
include "wi.mm"
include "wal.mm"
include "cplq.mm"
include "addclpr.mm"
include "adantr.mm"
include "df-plp.mm"
include "addclnq.mm"
include "genpprecl.mm"
include "imp.mm"
include "cltq.mm"
include "cnq.mm"
include "elprnq.mm"
include "cxp.mm"
include "addnqf.mm"
include "fdmi.mm"
include "0nnq.mm"
include "ndmovrcl.mm"
include "ltaddnq.mm"
include "3syl.mm"
include "prcdnq.mm"
include "mpd.mm"
include "syl2anc.mm"
include "exp32.mm"
include "com23.mm"
include "alrimdv.mm"
include "dfss2.mm"
include "syl6ibr.mm"
include "wrex.mm"
include "vex.mm"
include "prlem934.mm"
include "eleq2.mm"
include "biimprcd.mm"
include "con3d.mm"
include "syl6.mm"
include "expd.mm"
include "com34.mm"
include "rexlimdv.mm"
include "jcad.mm"
include "dfpss2.mm"
include "exlimdv.mm"
include "wb.mm"
include "ltprord.mm"
include "syldan.mm"
include "mpbird.mm"

theorem ltaddpr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- ( ( A e. P. /\ B e. P. ) -> A <P ( A +P. B ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cnp
    wcel
    #
    wa
    #
    cA
    cA
    cB
    cpp
    co
    #
    cltp
    wbr
    #
    cA
    @3
    wpss
    #
    @2
    vy
    cv
    #
    cB
    wcel
    #
    vy
    wex
    #
    @5
    @1
    @8
    @0
    @1
    cB
    c0
    wne
    @8
    cB
    prn0
    vy
    cB
    n0
    sylib
    adantl
    @2
    @7
    @5
    vy
    @2
    @7
    cA
    @3
    wss
    #
    cA
    @3
    wceq
    #
    wn
    #
    wa
    @5
    @2
    @7
    @9
    @11
    @2
    @7
    vx
    cv
    #
    cA
    wcel
    #
    @12
    @3
    wcel
    #
    wi
    #
    vx
    wal
    @9
    @2
    @7
    @15
    vx
    @2
    @13
    @7
    @14
    @2
    @13
    @7
    @14
    @2
    @13
    @7
    wa
    #
    wa
    @3
    cnp
    wcel
    #
    @12
    @6
    cplq
    co
    #
    @3
    wcel
    #
    @14
    @2
    @17
    @16
    cA
    cB
    addclpr
    #
    adantr
    @2
    @16
    @19
    vx
    vy
    vz
    vw
    vv
    cA
    cB
    @12
    @6
    cpp
    cplq
    vw
    vv
    vx
    vy
    vz
    df-plp
    @6
    vz
    cv
    addclnq
    genpprecl
    #
    imp
    @17
    @19
    wa
    #
    @12
    @18
    cltq
    wbr
    #
    @14
    @22
    @18
    cnq
    wcel
    @12
    cnq
    wcel
    @6
    cnq
    wcel
    wa
    @23
    @3
    @18
    elprnq
    @12
    @6
    cnq
    cplq
    cnq
    cnq
    cxp
    cnq
    cplq
    addnqf
    fdmi
    0nnq
    ndmovrcl
    @12
    @6
    ltaddnq
    3syl
    @3
    @18
    @12
    prcdnq
    mpd
    syl2anc
    exp32
    com23
    alrimdv
    vx
    cA
    @3
    dfss2
    syl6ibr
    @2
    @18
    cA
    wcel
    #
    wn
    #
    vx
    cA
    wrex
    #
    @7
    @11
    wi
    #
    @0
    @26
    @1
    vx
    cA
    @6
    vy
    vex
    prlem934
    adantr
    @2
    @25
    @27
    vx
    cA
    @2
    @13
    @7
    @25
    @11
    @2
    @13
    @7
    @25
    @11
    wi
    #
    @2
    @16
    @19
    @28
    @21
    @19
    @10
    @24
    @10
    @24
    @19
    cA
    @3
    @18
    eleq2
    biimprcd
    con3d
    syl6
    expd
    com34
    rexlimdv
    mpd
    jcad
    cA
    @3
    dfpss2
    syl6ibr
    exlimdv
    mpd
    @0
    @1
    @17
    @4
    @5
    wb
    @20
    cA
    @3
    ltprord
    syldan
    mpbird
end
