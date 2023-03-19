include "crngo.mm"
include "wcel.mm"
include "wne.mm"
include "cidl.mm"
include "cfv.mm"
include "csn.mm"
include "cpr.mm"
include "wceq.mm"
include "w3a.mm"
include "cpridl.mm"
include "cprrng.mm"
include "simp1.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "wo.mm"
include "wi.mm"
include "0idl.mm"
include "3ad2ant1.mm"
include "0rngo.mm"
include "eqcom.mm"
include "3bitr4g.mm"
include "necon3bid.mm"
include "biimpa.mm"
include "3adant3.mm"
include "wa.mm"
include "wb.mm"
include "cun.mm"
include "df-pr.mm"
include "eqeq2i.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "elun.mm"
include "velsn.mm"
include "orbi12i.mm"
include "bitri.mm"
include "anbi12i.mm"
include "syl6bb.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "eqimss.mm"
include "orcd.mm"
include "adantr.mm"
include "a1d.mm"
include "a1i.mm"
include "olcd.mm"
include "adantl.mm"
include "wn.mm"
include "wrex.mm"
include "crn.mm"
include "c1st.mm"
include "rneqi.mm"
include "eqtri.mm"
include "rngo1cl.mm"
include "rngolidm.mm"
include "mpdan.mm"
include "eleq1d.mm"
include "cgi.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elsn.mm"
include "necon3bbid.mm"
include "biimpar.mm"
include "oveq1.mm"
include "notbid.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "rexnal2.mm"
include "sylib.mm"
include "pm2.21d.mm"
include "raleq.mm"
include "ralbidv.mm"
include "sylan9bb.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "ccased.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "ispridl.mm"
include "mpbir3and.mm"
include "isprrngo.mm"
include "sylanbrc.mm"

theorem smprngopr
  let cR: class R
  let cU: class U
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume smprngpr.1: |- G = ( 1st ` R )
  assume smprngpr.2: |- H = ( 2nd ` R )
  assume smprngpr.3: |- X = ran G
  assume smprngpr.4: |- Z = ( GId ` G )
  assume smprngpr.5: |- U = ( GId ` H )


  assert |- ( ( R e. RingOps /\ U =/= Z /\ ( Idl ` R ) = { { Z } , X } ) -> R e. PrRing )

  proof
    cR
    crngo
    wcel
    #
    cU
    cZ
    wne
    #
    cR
    cidl
    cfv
    #
    cZ
    csn
    #
    cX
    cpr
    #
    wceq
    #
    w3a
    #
    @0
    @3
    cR
    cpridl
    cfv
    wcel
    #
    cR
    cprrng
    wcel
    @0
    @1
    @5
    simp1
    @6
    @7
    @3
    @2
    wcel
    #
    @3
    cX
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    @3
    wcel
    #
    vy
    vj
    cv
    #
    wral
    #
    vx
    vi
    cv
    #
    wral
    #
    @16
    @3
    wss
    #
    @14
    @3
    wss
    #
    wo
    #
    wi
    #
    vj
    @2
    wral
    vi
    @2
    wral
    #
    @0
    @1
    @8
    @5
    cR
    cG
    cZ
    smprngpr.1
    smprngpr.4
    0idl
    3ad2ant1
    @0
    @1
    @9
    @5
    @0
    @1
    @9
    @0
    cU
    cZ
    @3
    cX
    @0
    cZ
    cU
    wceq
    cX
    @3
    wceq
    cU
    cZ
    wceq
    #
    @3
    cX
    wceq
    cR
    cU
    cG
    cH
    cX
    cZ
    smprngpr.1
    smprngpr.2
    smprngpr.3
    smprngpr.4
    smprngpr.5
    0rngo
    cU
    cZ
    eqcom
    @3
    cX
    eqcom
    3bitr4g
    necon3bid
    biimpa
    3adant3
    @6
    @21
    vi
    vj
    @2
    @2
    @6
    @16
    @2
    wcel
    #
    @14
    @2
    wcel
    #
    wa
    #
    @16
    @3
    wceq
    #
    @16
    cX
    wceq
    #
    wo
    #
    @14
    @3
    wceq
    #
    @14
    cX
    wceq
    #
    wo
    #
    wa
    #
    @21
    @5
    @0
    @26
    @33
    wb
    #
    @1
    @5
    @2
    @3
    csn
    #
    cX
    csn
    #
    cun
    #
    wceq
    #
    @34
    @4
    @37
    @2
    @3
    cX
    df-pr
    eqeq2i
    @38
    @26
    @16
    @37
    wcel
    #
    @14
    @37
    wcel
    #
    wa
    @33
    @38
    @24
    @39
    @25
    @40
    @2
    @37
    @16
    eleq2
    @2
    @37
    @14
    eleq2
    anbi12d
    @39
    @29
    @40
    @32
    @39
    @16
    @35
    wcel
    #
    @16
    @36
    wcel
    #
    wo
    @29
    @16
    @35
    @36
    elun
    @41
    @27
    @42
    @28
    vi
    @3
    velsn
    vi
    cX
    velsn
    orbi12i
    bitri
    @40
    @14
    @35
    wcel
    #
    @14
    @36
    wcel
    #
    wo
    @32
    @14
    @35
    @36
    elun
    @43
    @30
    @44
    @31
    vj
    @3
    velsn
    vj
    cX
    velsn
    orbi12i
    bitri
    anbi12i
    syl6bb
    sylbi
    3ad2ant3
    @0
    @1
    @33
    @21
    wi
    @5
    @0
    @1
    wa
    #
    @27
    @30
    @28
    @31
    @21
    @27
    @30
    wa
    #
    @21
    wi
    @45
    @46
    @20
    @17
    @27
    @20
    @30
    @27
    @18
    @19
    @16
    @3
    eqimss
    orcd
    #
    adantr
    a1d
    a1i
    @28
    @30
    wa
    #
    @21
    wi
    @45
    @48
    @20
    @17
    @30
    @20
    @28
    @30
    @19
    @18
    @14
    @3
    eqimss
    olcd
    adantl
    a1d
    a1i
    @27
    @31
    wa
    #
    @21
    wi
    @45
    @49
    @20
    @17
    @27
    @20
    @31
    @47
    adantr
    a1d
    a1i
    @45
    @21
    @28
    @31
    wa
    #
    @13
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    @20
    wi
    @45
    @52
    @20
    @45
    @13
    wn
    #
    vy
    cX
    wrex
    vx
    cX
    wrex
    #
    @52
    wn
    @45
    cU
    cX
    wcel
    #
    @55
    cU
    cU
    cH
    co
    #
    @3
    wcel
    #
    wn
    #
    @54
    @0
    @55
    @1
    cR
    cU
    cH
    cX
    cX
    cG
    crn
    cR
    c1st
    cfv
    #
    crn
    smprngpr.3
    cG
    @59
    smprngpr.1
    rneqi
    eqtri
    #
    smprngpr.2
    smprngpr.5
    rngo1cl
    #
    adantr
    #
    @62
    @0
    @58
    @1
    @0
    @57
    cU
    cZ
    @0
    @57
    cU
    @3
    wcel
    @23
    @0
    @56
    cU
    @3
    @0
    @55
    @56
    cU
    wceq
    @61
    cU
    cR
    cU
    cH
    cX
    smprngpr.2
    @60
    smprngpr.5
    rngolidm
    mpdan
    eleq1d
    cU
    cZ
    cU
    cH
    cgi
    cfv
    cvv
    smprngpr.5
    cH
    cgi
    fvex
    eqeltri
    elsn
    syl6bb
    necon3bbid
    biimpar
    @53
    @58
    cU
    @11
    cH
    co
    #
    @3
    wcel
    #
    wn
    vx
    vy
    cU
    cU
    cX
    cX
    @10
    cU
    wceq
    #
    @13
    @64
    @65
    @12
    @63
    @3
    @10
    cU
    @11
    cH
    oveq1
    eleq1d
    notbid
    @11
    cU
    wceq
    #
    @64
    @57
    @66
    @63
    @56
    @3
    @11
    cU
    cU
    cH
    oveq2
    eleq1d
    notbid
    rspc2ev
    syl3anc
    @13
    vx
    vy
    cX
    cX
    rexnal2
    sylib
    pm2.21d
    @50
    @17
    @52
    @20
    @28
    @17
    @15
    vx
    cX
    wral
    @31
    @52
    @15
    vx
    @16
    cX
    raleq
    @31
    @15
    @51
    vx
    cX
    @13
    vy
    @14
    cX
    raleq
    ralbidv
    sylan9bb
    imbi1d
    syl5ibrcom
    ccased
    3adant3
    sylbid
    ralrimivv
    @0
    @1
    @7
    @8
    @9
    @22
    w3a
    wb
    @5
    vx
    vy
    @3
    cR
    cG
    cH
    cX
    vi
    vj
    smprngpr.1
    smprngpr.2
    smprngpr.3
    ispridl
    3ad2ant1
    mpbir3and
    cR
    cG
    cZ
    smprngpr.1
    smprngpr.4
    isprrngo
    sylanbrc
end
