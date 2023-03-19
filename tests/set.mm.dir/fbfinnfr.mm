include "cfbas.mm"
include "cfv.mm"
include "wcel.mm"
include "cfn.mm"
include "cint.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "imbi1d.mm"
include "wpss.mm"
include "wal.mm"
include "wral.mm"
include "wb.mm"
include "ibar.mm"
include "adantr.mm"
include "bi2.04.mm"
include "syl6rbbr.mm"
include "albidv.mm"
include "df-ral.mm"
include "syl6bbr.mm"
include "wss.mm"
include "wn.mm"
include "0nelfb.mm"
include "notbid.mm"
include "syl5ibrcom.mm"
include "necon2ad.mm"
include "imp.mm"
include "ssn0.mm"
include "ex.mm"
include "syl5com.mm"
include "a1dd.mm"
include "wrex.mm"
include "ssint.mm"
include "notbii.mm"
include "rexnal.mm"
include "bitr4i.mm"
include "w3a.mm"
include "cin.mm"
include "fbasssin.mm"
include "nssinpss.mm"
include "sspsstr.mm"
include "sylan2b.mm"
include "expcom.mm"
include "reximdv.mm"
include "3expia.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "r19.29.mm"
include "id.mm"
include "rexlimivw.mm"
include "syl.mm"
include "syl6.mm"
include "pm2.61d.mm"
include "sylbid.mm"
include "com12.mm"
include "a1i.mm"
include "findcard3.mm"
include "3impia.mm"

theorem fbfinnfr
  let cB: class B
  let cS: class S
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( F e. ( fBas ` B ) /\ S e. F /\ S e. Fin ) -> |^| F =/= (/) )

  proof
    cF
    cB
    cfbas
    cfv
    wcel
    #
    cS
    cF
    wcel
    #
    cS
    cfn
    wcel
    #
    cF
    cint
    #
    c0
    wne
    #
    @2
    @0
    @1
    wa
    #
    @4
    @0
    vx
    cv
    #
    cF
    wcel
    #
    wa
    #
    @4
    wi
    #
    @0
    vy
    cv
    #
    cF
    wcel
    #
    wa
    #
    @4
    wi
    #
    @5
    @4
    wi
    vx
    vy
    cS
    @6
    @10
    wceq
    #
    @8
    @12
    @4
    @14
    @7
    @11
    @0
    @6
    @10
    cF
    eleq1
    anbi2d
    imbi1d
    @6
    cS
    wceq
    #
    @8
    @5
    @4
    @15
    @7
    @1
    @0
    @6
    cS
    cF
    eleq1
    anbi2d
    imbi1d
    @6
    @10
    wpss
    #
    @9
    wi
    #
    vx
    wal
    #
    @13
    wi
    @10
    cfn
    wcel
    @12
    @18
    @4
    @12
    @18
    @16
    @4
    wi
    #
    vx
    cF
    wral
    #
    @4
    @12
    @18
    @7
    @19
    wi
    #
    vx
    wal
    @20
    @12
    @17
    @21
    vx
    @12
    @21
    @8
    @19
    wi
    @17
    @12
    @7
    @8
    @19
    @0
    @7
    @8
    wb
    @11
    @0
    @7
    ibar
    adantr
    imbi1d
    @16
    @8
    @4
    bi2.04
    syl6rbbr
    albidv
    @19
    vx
    cF
    df-ral
    syl6bbr
    @12
    @10
    @3
    wss
    #
    @20
    @4
    wi
    #
    @12
    @22
    @4
    @20
    @12
    @10
    c0
    wne
    #
    @22
    @4
    @0
    @11
    @24
    @0
    @11
    @10
    c0
    @0
    @11
    wn
    @10
    c0
    wceq
    #
    c0
    cF
    wcel
    #
    wn
    cB
    cF
    0nelfb
    @25
    @11
    @26
    @10
    c0
    cF
    eleq1
    notbid
    syl5ibrcom
    necon2ad
    imp
    @22
    @24
    @4
    @10
    @3
    ssn0
    ex
    syl5com
    a1dd
    @12
    @22
    wn
    #
    @16
    vx
    cF
    wrex
    #
    @23
    @27
    @10
    vz
    cv
    #
    wss
    #
    wn
    #
    vz
    cF
    wrex
    #
    @12
    @28
    @27
    @30
    vz
    cF
    wral
    #
    wn
    @32
    @22
    @33
    vz
    @10
    cF
    ssint
    notbii
    @30
    vz
    cF
    rexnal
    bitr4i
    @12
    @31
    @28
    vz
    cF
    @0
    @11
    @29
    cF
    wcel
    #
    @31
    @28
    wi
    @0
    @11
    @34
    w3a
    @6
    @10
    @29
    cin
    #
    wss
    #
    vx
    cF
    wrex
    @31
    @28
    vx
    @10
    @29
    cF
    cB
    fbasssin
    @31
    @36
    @16
    vx
    cF
    @36
    @31
    @16
    @31
    @36
    @35
    @10
    wpss
    @16
    @10
    @29
    nssinpss
    @6
    @35
    @10
    sspsstr
    sylan2b
    expcom
    reximdv
    syl5com
    3expia
    rexlimdv
    syl5bi
    @20
    @28
    @4
    @20
    @28
    wa
    @19
    @16
    wa
    #
    vx
    cF
    wrex
    @4
    @19
    @16
    vx
    cF
    r19.29
    @37
    @4
    vx
    cF
    @19
    @16
    @4
    @19
    id
    imp
    rexlimivw
    syl
    expcom
    syl6
    pm2.61d
    sylbid
    com12
    a1i
    findcard3
    com12
    3impia
end
