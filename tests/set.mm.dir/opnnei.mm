include "ctop.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "wral.mm"
include "wb.mm"
include "wa.mm"
include "0opn.mm"
include "adantr.mm"
include "eleq1.mm"
include "adantl.mm"
include "mpbird.mm"
include "rzal.mm"
include "2thd.mm"
include "wn.mm"
include "wi.mm"
include "opnneip.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "ex.mm"
include "cuni.mm"
include "wss.mm"
include "wrex.mm"
include "wne.mm"
include "df-ne.mm"
include "r19.2z.mm"
include "sylbir.mm"
include "eqid.mm"
include "neii1.mm"
include "rexlimdvw.mm"
include "sylan9r.mm"
include "cnt.mm"
include "ntrss2.mm"
include "vex.mm"
include "snss.mm"
include "ralbii.mm"
include "dfss3.mm"
include "biimpri.mm"
include "sylan2br.mm"
include "eqssd.mm"
include "sstr2.mm"
include "com12.mm"
include "syl5bi.mm"
include "imp.mm"
include "neiint.mm"
include "3com23.mm"
include "3expa.mm"
include "syldan.mm"
include "ralbidva.mm"
include "isopn3.mm"
include "3imtr4d.mm"
include "com23.mm"
include "mpdd.mm"
include "impbid.mm"
include "pm2.61dan.mm"

theorem opnnei
  let vx: setvar x
  let cS: class S
  let cJ: class J

  disjoint J x
  disjoint S x
  assert |- ( J e. Top -> ( S e. J <-> A. x e. S S e. ( ( nei ` J ) ` { x } ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cS
    c0
    wceq
    #
    cS
    cJ
    wcel
    #
    cS
    vx
    cv
    #
    csn
    #
    cJ
    cnei
    cfv
    cfv
    wcel
    #
    vx
    cS
    wral
    #
    wb
    @0
    @1
    wa
    #
    @2
    @6
    @7
    @2
    c0
    cJ
    wcel
    #
    @0
    @8
    @1
    cJ
    0opn
    adantr
    @1
    @2
    @8
    wb
    @0
    cS
    c0
    cJ
    eleq1
    adantl
    mpbird
    @1
    @6
    @0
    @5
    vx
    cS
    rzal
    adantl
    2thd
    @0
    @1
    wn
    #
    wa
    #
    @2
    @6
    @0
    @2
    @6
    wi
    @9
    @0
    @2
    @6
    @0
    @2
    wa
    @5
    vx
    cS
    @0
    @2
    @3
    cS
    wcel
    #
    @5
    @3
    cJ
    cS
    opnneip
    3expia
    ralrimiv
    ex
    adantr
    @10
    @6
    cS
    cJ
    cuni
    #
    wss
    #
    @2
    @9
    @6
    @5
    vx
    cS
    wrex
    #
    @0
    @13
    @9
    cS
    c0
    wne
    #
    @6
    @14
    wi
    cS
    c0
    df-ne
    @15
    @6
    @14
    @5
    vx
    cS
    r19.2z
    ex
    sylbir
    @0
    @5
    @13
    vx
    cS
    @0
    @5
    @13
    @4
    cJ
    cS
    @12
    @12
    eqid
    #
    neii1
    ex
    rexlimdvw
    sylan9r
    @0
    @6
    @13
    @2
    wi
    wi
    @9
    @0
    @13
    @6
    @2
    @0
    @13
    @6
    @2
    wi
    @0
    @13
    wa
    #
    @4
    cS
    cJ
    cnt
    cfv
    cfv
    #
    wss
    #
    vx
    cS
    wral
    #
    @18
    cS
    wceq
    #
    @6
    @2
    @17
    @20
    @21
    @17
    @20
    wa
    @18
    cS
    @17
    @18
    cS
    wss
    @20
    cS
    cJ
    @12
    @16
    ntrss2
    adantr
    @20
    @17
    @3
    @18
    wcel
    #
    vx
    cS
    wral
    #
    cS
    @18
    wss
    #
    @22
    @19
    vx
    cS
    @3
    @18
    vx
    vex
    #
    snss
    ralbii
    @23
    @24
    @17
    @24
    @23
    vx
    cS
    @18
    dfss3
    biimpri
    adantl
    sylan2br
    eqssd
    ex
    @17
    @5
    @19
    vx
    cS
    @17
    @11
    @4
    @12
    wss
    #
    @5
    @19
    wb
    #
    @17
    @11
    @26
    @11
    @4
    cS
    wss
    #
    @17
    @26
    @3
    cS
    @25
    snss
    @13
    @28
    @26
    wi
    @0
    @28
    @13
    @26
    @4
    cS
    @12
    sstr2
    com12
    adantl
    syl5bi
    imp
    @0
    @13
    @26
    @27
    @0
    @26
    @13
    @27
    @4
    cJ
    cS
    @12
    @16
    neiint
    3com23
    3expa
    syldan
    ralbidva
    cS
    cJ
    @12
    @16
    isopn3
    3imtr4d
    ex
    com23
    adantr
    mpdd
    impbid
    pm2.61dan
end
