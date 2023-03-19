include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "c0.mm"
include "csuc.mm"
include "breq1.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "ensym.mm"
include "en0.mm"
include "eqcom.mm"
include "bitri.mm"
include "sylib.mm"
include "rgenw.mm"
include "wrex.mm"
include "wo.mm"
include "nn0suc.mm"
include "wb.mm"
include "breq2.mm"
include "eqeq2.mm"
include "bibi12d.mm"
include "mpbiri.mm"
include "biimpd.mm"
include "a1i.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "rsp.mm"
include "vex.mm"
include "phplem4.mm"
include "imim1d.mm"
include "ex.mm"
include "a2d.mm"
include "syl5.mm"
include "imp.mm"
include "suceq.mm"
include "syl8.mm"
include "biimprcd.mm"
include "syl6.mm"
include "rexlimd.mm"
include "jaod.mm"
include "syl7.mm"
include "ralrimdv.mm"
include "cbvralv.mm"
include "syl6ib.mm"
include "finds.mm"
include "rspcv.mm"
include "mpan9.mm"
include "eqeng.mm"
include "adantr.mm"
include "impbid.mm"

theorem nneneq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A e. _om /\ B e. _om ) -> ( A ~~ B <-> A = B ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    wa
    cA
    cB
    cen
    wbr
    #
    cA
    cB
    wceq
    #
    @0
    cA
    vz
    cv
    #
    cen
    wbr
    #
    cA
    @4
    wceq
    #
    wi
    #
    vz
    com
    wral
    #
    @1
    @2
    @3
    wi
    #
    vx
    cv
    #
    @4
    cen
    wbr
    #
    @10
    @4
    wceq
    #
    wi
    #
    vz
    com
    wral
    c0
    @4
    cen
    wbr
    #
    c0
    @4
    wceq
    #
    wi
    #
    vz
    com
    wral
    vy
    cv
    #
    @4
    cen
    wbr
    #
    @17
    @4
    wceq
    #
    wi
    #
    vz
    com
    wral
    #
    @17
    csuc
    #
    @4
    cen
    wbr
    #
    @22
    @4
    wceq
    #
    wi
    #
    vz
    com
    wral
    #
    @8
    vx
    vy
    cA
    @10
    c0
    wceq
    #
    @13
    @16
    vz
    com
    @27
    @11
    @14
    @12
    @15
    @10
    c0
    @4
    cen
    breq1
    @10
    c0
    @4
    eqeq1
    imbi12d
    ralbidv
    @10
    @17
    wceq
    #
    @13
    @20
    vz
    com
    @28
    @11
    @18
    @12
    @19
    @10
    @17
    @4
    cen
    breq1
    @10
    @17
    @4
    eqeq1
    imbi12d
    ralbidv
    @10
    @22
    wceq
    #
    @13
    @25
    vz
    com
    @29
    @11
    @23
    @12
    @24
    @10
    @22
    @4
    cen
    breq1
    @10
    @22
    @4
    eqeq1
    imbi12d
    ralbidv
    @10
    cA
    wceq
    #
    @13
    @7
    vz
    com
    @30
    @11
    @5
    @12
    @6
    @10
    cA
    @4
    cen
    breq1
    @10
    cA
    @4
    eqeq1
    imbi12d
    ralbidv
    @16
    vz
    com
    @14
    @4
    c0
    cen
    wbr
    #
    @15
    c0
    @4
    ensym
    @31
    @4
    c0
    wceq
    @15
    @4
    en0
    @4
    c0
    eqcom
    bitri
    sylib
    rgenw
    @17
    com
    wcel
    #
    @21
    @22
    vw
    cv
    #
    cen
    wbr
    #
    @22
    @33
    wceq
    #
    wi
    #
    vw
    com
    wral
    @26
    @32
    @21
    @36
    vw
    com
    @33
    com
    wcel
    @33
    c0
    wceq
    #
    @33
    @4
    csuc
    #
    wceq
    #
    vz
    com
    wrex
    #
    wo
    #
    @32
    @21
    @36
    vz
    @33
    nn0suc
    @32
    @21
    @41
    @36
    wi
    @32
    @21
    wa
    #
    @37
    @36
    @40
    @37
    @36
    wi
    @42
    @37
    @34
    @35
    @37
    @34
    @35
    wb
    @22
    c0
    cen
    wbr
    #
    @22
    c0
    wceq
    #
    wb
    @22
    en0
    @37
    @34
    @43
    @35
    @44
    @33
    c0
    @22
    cen
    breq2
    @33
    c0
    @22
    eqeq2
    bibi12d
    mpbiri
    biimpd
    a1i
    @42
    @39
    @36
    vz
    com
    @32
    @21
    vz
    @32
    vz
    nfv
    @20
    vz
    com
    nfra1
    nfan
    @36
    vz
    nfv
    @42
    @4
    com
    wcel
    #
    @22
    @38
    cen
    wbr
    #
    @22
    @38
    wceq
    #
    wi
    #
    @39
    @36
    wi
    @42
    @45
    @46
    @19
    @47
    @32
    @21
    @45
    @46
    @19
    wi
    #
    wi
    #
    @21
    @45
    @20
    wi
    @32
    @50
    @20
    vz
    com
    rsp
    @32
    @45
    @20
    @49
    @32
    @45
    @20
    @49
    wi
    @32
    @45
    wa
    @46
    @18
    @19
    @17
    @4
    vy
    vex
    vz
    vex
    phplem4
    imim1d
    ex
    a2d
    syl5
    imp
    @17
    @4
    suceq
    syl8
    @39
    @36
    @48
    @39
    @34
    @46
    @35
    @47
    @33
    @38
    @22
    cen
    breq2
    @33
    @38
    @22
    eqeq2
    imbi12d
    biimprcd
    syl6
    rexlimd
    jaod
    ex
    syl7
    ralrimdv
    @36
    @25
    vw
    vz
    com
    @33
    @4
    wceq
    @34
    @23
    @35
    @24
    @33
    @4
    @22
    cen
    breq2
    @33
    @4
    @22
    eqeq2
    imbi12d
    cbvralv
    syl6ib
    finds
    @7
    @9
    vz
    cB
    com
    @4
    cB
    wceq
    @5
    @2
    @6
    @3
    @4
    cB
    cA
    cen
    breq2
    @4
    cB
    cA
    eqeq2
    imbi12d
    rspcv
    mpan9
    @0
    @3
    @2
    wi
    @1
    cA
    cB
    com
    eqeng
    adantr
    impbid
end
