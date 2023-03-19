include "ccat.mm"
include "wcel.mm"
include "chomf.mm"
include "cfv.mm"
include "csubc.mm"
include "cssc.mm"
include "wbr.mm"
include "cv.mm"
include "ccid.mm"
include "co.mm"
include "cop.mm"
include "cco.mm"
include "wral.mm"
include "cbs.mm"
include "wa.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "cxp.mm"
include "wfn.mm"
include "eqid.mm"
include "homffn.mm"
include "fvexd.mm"
include "isssc.mm"
include "mpbir2and.mm"
include "chom.mm"
include "simpl.mm"
include "simpr.mm"
include "catidcl.mm"
include "homfval.mm"
include "eleqtrrd.mm"
include "adantr.mm"
include "adantl.mm"
include "wi.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "impcom.mm"
include "biimpd.mm"
include "adantld.mm"
include "imp.mm"
include "catcocl.mm"
include "wceq.mm"
include "jca.mm"
include "ralrimiva.mm"
include "id.mm"
include "issubc2.mm"

theorem catsubcat
  let cC: class C
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( C e. Cat -> ( Homf ` C ) e. ( Subcat ` C ) )

  proof
    cC
    ccat
    wcel
    #
    cC
    chomf
    cfv
    #
    cC
    csubc
    cfv
    wcel
    @1
    @1
    cssc
    wbr
    #
    vx
    cv
    #
    cC
    ccid
    cfv
    #
    cfv
    #
    @3
    @3
    @1
    co
    #
    wcel
    #
    vg
    cv
    #
    vf
    cv
    #
    @3
    vy
    cv
    #
    cop
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    co
    #
    @3
    @11
    @1
    co
    #
    wcel
    #
    vg
    @10
    @11
    @1
    co
    #
    wral
    vf
    @3
    @10
    @1
    co
    #
    wral
    #
    vz
    cC
    cbs
    cfv
    #
    wral
    vy
    @19
    wral
    #
    wa
    #
    vx
    @19
    wral
    @0
    @2
    @19
    @19
    wss
    #
    @17
    @17
    wss
    #
    vy
    @19
    wral
    vx
    @19
    wral
    @22
    @0
    @19
    ssid
    a1i
    @0
    @23
    vx
    vy
    @19
    @19
    @23
    @0
    @3
    @19
    wcel
    #
    @10
    @19
    wcel
    #
    wa
    wa
    @17
    ssid
    a1i
    ralrimivva
    @0
    vx
    vy
    @19
    @19
    @1
    @1
    cvv
    @1
    @19
    @19
    cxp
    wfn
    @0
    @19
    cC
    @1
    @1
    eqid
    #
    @19
    eqid
    #
    homffn
    a1i
    #
    @28
    @0
    cC
    cbs
    fvexd
    isssc
    mpbir2and
    @0
    @21
    vx
    @19
    @0
    @24
    wa
    #
    @7
    @20
    @29
    @5
    @3
    @3
    cC
    chom
    cfv
    #
    co
    @6
    @29
    @19
    cC
    @4
    @30
    @3
    @27
    @30
    eqid
    #
    @4
    eqid
    #
    @0
    @24
    simpl
    #
    @0
    @24
    simpr
    #
    catidcl
    @29
    @19
    cC
    @1
    @30
    @3
    @3
    @26
    @27
    @31
    @34
    @34
    homfval
    eleqtrrd
    @29
    @18
    vy
    vz
    @19
    @19
    @29
    @25
    @11
    @19
    wcel
    #
    wa
    #
    wa
    #
    @15
    vf
    vg
    @17
    @16
    @37
    @9
    @17
    wcel
    #
    @8
    @16
    wcel
    #
    wa
    #
    wa
    #
    @13
    @3
    @11
    @30
    co
    #
    @14
    @41
    @19
    cC
    @12
    @9
    @8
    @30
    @3
    @10
    @11
    @27
    @31
    @12
    eqid
    #
    @37
    @0
    @40
    @29
    @0
    @36
    @33
    adantr
    adantr
    @37
    @24
    @40
    @29
    @24
    @36
    @34
    adantr
    #
    adantr
    @37
    @25
    @40
    @36
    @25
    @29
    @25
    @35
    simpl
    adantl
    #
    adantr
    @37
    @35
    @40
    @36
    @35
    @29
    @25
    @35
    simpr
    adantl
    #
    adantr
    @40
    @37
    @9
    @3
    @10
    @30
    co
    #
    wcel
    #
    @38
    @37
    @48
    wi
    @39
    @37
    @38
    @48
    @37
    @17
    @47
    @9
    @37
    @19
    cC
    @1
    @30
    @3
    @10
    @26
    @27
    @31
    @44
    @45
    homfval
    eleq2d
    biimpcd
    adantr
    impcom
    @37
    @40
    @8
    @10
    @11
    @30
    co
    #
    wcel
    #
    @37
    @39
    @50
    @38
    @37
    @39
    @50
    @37
    @16
    @49
    @8
    @37
    @19
    cC
    @1
    @30
    @10
    @11
    @26
    @27
    @31
    @45
    @46
    homfval
    eleq2d
    biimpd
    adantld
    imp
    catcocl
    @37
    @14
    @42
    wceq
    @40
    @37
    @19
    cC
    @1
    @30
    @3
    @11
    @26
    @27
    @31
    @44
    @46
    homfval
    adantr
    eleqtrrd
    ralrimivva
    ralrimivva
    jca
    ralrimiva
    @0
    vx
    vy
    vz
    cC
    @19
    @12
    @4
    vf
    vg
    @1
    @1
    @26
    @32
    @43
    @0
    id
    @28
    issubc2
    mpbir2and
end
