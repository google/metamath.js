include "cdrng.mm"
include "wcel.mm"
include "crngo.mm"
include "cgi.mm"
include "cfv.mm"
include "wne.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cidl.mm"
include "cpr.mm"
include "eqid.mm"
include "isdrngo2.mm"
include "wo.mm"
include "wi.mm"
include "idl0cl.mm"
include "adantr.mm"
include "wex.mm"
include "wss.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snss.mm"
include "necom.mm"
include "c0.mm"
include "pssdifn0.mm"
include "n0.mm"
include "sylib.mm"
include "syl2anb.mm"
include "idlss.mm"
include "ssdif.mm"
include "sselda.mm"
include "sylan.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "eldifi.mm"
include "anim12i.mm"
include "idllmulcl.mm"
include "1idl.mm"
include "biimpd.mm"
include "eleq1.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "mpid.mm"
include "sylan2.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "imp.mm"
include "syldan.mm"
include "an32s.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5.mm"
include "mpand.mm"
include "neor.mm"
include "sylibr.mm"
include "0idl.mm"
include "rngoidl.mm"
include "jaod.mm"
include "impbid.mm"
include "vex.mm"
include "elpr.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "adantrl.mm"
include "sylbi.mm"

theorem divrngidl
  let cR: class R
  let cG: class G
  let cH: class H
  let cX: class X
  let cZ: class Z
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume divrngidl.1: |- G = ( 1st ` R )
  assume divrngidl.2: |- H = ( 2nd ` R )
  assume divrngidl.3: |- X = ran G
  assume divrngidl.4: |- Z = ( GId ` G )


  assert |- ( R e. DivRingOps -> ( Idl ` R ) = { { Z } , X } )

  proof
    cR
    cdrng
    wcel
    cR
    crngo
    wcel
    #
    cH
    cgi
    cfv
    #
    cZ
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cH
    co
    #
    @1
    wceq
    #
    vy
    cX
    cZ
    csn
    #
    cdif
    #
    wrex
    #
    vx
    @8
    wral
    #
    wa
    wa
    cR
    cidl
    cfv
    #
    @7
    cX
    cpr
    #
    wceq
    #
    vx
    vy
    cR
    @1
    cG
    cH
    cX
    cZ
    divrngidl.1
    divrngidl.2
    divrngidl.4
    divrngidl.3
    @1
    eqid
    #
    isdrngo2
    @0
    @10
    @13
    @2
    @0
    @10
    wa
    #
    vi
    @11
    @12
    @15
    vi
    cv
    #
    @11
    wcel
    #
    @16
    @7
    wceq
    #
    @16
    cX
    wceq
    #
    wo
    #
    @16
    @12
    wcel
    @15
    @17
    @20
    @15
    @17
    @20
    @15
    @17
    wa
    @16
    @7
    wne
    #
    @19
    wi
    #
    @20
    @0
    @17
    @10
    @22
    @0
    @17
    wa
    #
    @10
    wa
    #
    cZ
    @16
    wcel
    #
    @21
    @19
    @23
    @25
    @10
    cR
    cG
    @16
    cZ
    divrngidl.1
    divrngidl.4
    idl0cl
    adantr
    @25
    @21
    wa
    vz
    cv
    #
    @16
    @7
    cdif
    #
    wcel
    #
    vz
    wex
    #
    @24
    @19
    @25
    @7
    @16
    wss
    #
    @7
    @16
    wne
    #
    @29
    @21
    cZ
    @16
    cZ
    cG
    cgi
    cfv
    cvv
    divrngidl.4
    cG
    cgi
    fvex
    eqeltri
    snss
    @16
    @7
    necom
    @30
    @31
    wa
    @27
    c0
    wne
    @29
    @7
    @16
    pssdifn0
    vz
    @27
    n0
    sylib
    syl2anb
    @24
    @28
    @19
    vz
    @24
    @28
    @19
    @23
    @28
    @10
    @19
    @23
    @28
    wa
    #
    @10
    @3
    @26
    cH
    co
    #
    @1
    wceq
    #
    vy
    @8
    wrex
    #
    @19
    @32
    @26
    @8
    wcel
    #
    @10
    @35
    @23
    @16
    cX
    wss
    #
    @28
    @36
    cR
    cG
    @16
    cX
    divrngidl.1
    divrngidl.3
    idlss
    @37
    @27
    @8
    @26
    @16
    cX
    @7
    ssdif
    sselda
    sylan
    @9
    @35
    vx
    @26
    @8
    @4
    @26
    wceq
    #
    @6
    @34
    vy
    @8
    @38
    @5
    @33
    @1
    @4
    @26
    @3
    cH
    oveq2
    eqeq1d
    rexbidv
    rspcva
    sylan
    @32
    @35
    @19
    @32
    @34
    @19
    vy
    @8
    @23
    @28
    @3
    @8
    wcel
    #
    @34
    @19
    wi
    #
    @28
    @39
    wa
    @23
    @26
    @16
    wcel
    #
    @3
    cX
    wcel
    #
    wa
    #
    @40
    @28
    @41
    @39
    @42
    @26
    @16
    @7
    eldifi
    @3
    cX
    @7
    eldifi
    anim12i
    @23
    @43
    wa
    #
    @34
    @33
    @16
    wcel
    #
    @19
    @26
    @3
    cR
    cG
    cH
    @16
    cX
    divrngidl.1
    divrngidl.2
    divrngidl.3
    idllmulcl
    @44
    @45
    @19
    wi
    @34
    @1
    @16
    wcel
    #
    @19
    wi
    #
    @23
    @47
    @43
    @23
    @46
    @19
    cR
    @1
    cG
    cH
    @16
    cX
    divrngidl.1
    divrngidl.2
    divrngidl.3
    @14
    1idl
    biimpd
    adantr
    @34
    @45
    @46
    @19
    @33
    @1
    @16
    eleq1
    imbi1d
    syl5ibrcom
    mpid
    sylan2
    anassrs
    rexlimdva
    imp
    syldan
    an32s
    ex
    exlimdv
    syl5
    mpand
    an32s
    @19
    @16
    @7
    neor
    sylibr
    ex
    @0
    @20
    @17
    wi
    @10
    @0
    @18
    @17
    @19
    @0
    @17
    @18
    @7
    @11
    wcel
    cR
    cG
    cZ
    divrngidl.1
    divrngidl.4
    0idl
    @16
    @7
    @11
    eleq1
    syl5ibrcom
    @0
    @17
    @19
    cX
    @11
    wcel
    cR
    cG
    cX
    divrngidl.1
    divrngidl.3
    rngoidl
    @16
    cX
    @11
    eleq1
    syl5ibrcom
    jaod
    adantr
    impbid
    @16
    @7
    cX
    vi
    vex
    elpr
    syl6bbr
    eqrdv
    adantrl
    sylbi
end
