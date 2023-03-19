include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "cdm.mm"
include "ccnv.mm"
include "cr.mm"
include "cima.mm"
include "cnvimass.mm"
include "eqsstri.mm"
include "cxr.mm"
include "wf.mm"
include "wceq.mm"
include "xmetf.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "relxp.mm"
include "relss.mm"
include "mpisyl.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "co.mm"
include "w3a.mm"
include "xmeterval.mm"
include "biimpa.mm"
include "simp2d.mm"
include "simp1d.mm"
include "simpl.mm"
include "xmetsym.mm"
include "syl3anc.mm"
include "simp3d.mm"
include "eqeltrrd.mm"
include "wb.mm"
include "adantr.mm"
include "mpbir3and.mm"
include "adantrr.mm"
include "adantrl.mm"
include "cxad.mm"
include "cle.mm"
include "caddc.mm"
include "rexadd.mm"
include "readdcl.mm"
include "eqeltrd.mm"
include "syl2anc.mm"
include "xmettri.mm"
include "syl13anc.mm"
include "xmetlecl.mm"
include "syl122anc.mm"
include "cc0.mm"
include "xmet0.mm"
include "0re.mm"
include "syl6eqel.mm"
include "ex.mm"
include "pm4.71rd.mm"
include "df-3an.mm"
include "anidm.mm"
include "anbi2ci.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "bitr4d.mm"
include "iserd.mm"

theorem xmeter
  let cD: class D
  let c.sm: class .~
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  assume xmeter.1: |- .~ = ( `' D " RR )


  assert |- ( D e. ( *Met ` X ) -> .~ Er X )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    vx
    vy
    vz
    cX
    c.sm
    @0
    c.sm
    cX
    cX
    cxp
    #
    wss
    @1
    wrel
    c.sm
    wrel
    @0
    cD
    cdm
    #
    c.sm
    @1
    c.sm
    cD
    ccnv
    cr
    cima
    @2
    xmeter.1
    cD
    cr
    cnvimass
    eqsstri
    @0
    @1
    cxr
    cD
    wf
    @2
    @1
    wceq
    cD
    cX
    xmetf
    @1
    cxr
    cD
    fdm
    syl
    syl5sseq
    cX
    cX
    relxp
    c.sm
    @1
    relss
    mpisyl
    @0
    vx
    cv
    #
    vy
    cv
    #
    c.sm
    wbr
    #
    wa
    #
    @4
    @3
    c.sm
    wbr
    #
    @4
    cX
    wcel
    #
    @3
    cX
    wcel
    #
    @4
    @3
    cD
    co
    #
    cr
    wcel
    #
    @6
    @9
    @8
    @3
    @4
    cD
    co
    #
    cr
    wcel
    #
    @0
    @5
    @9
    @8
    @13
    w3a
    @3
    @4
    cD
    c.sm
    cX
    xmeter.1
    xmeterval
    biimpa
    #
    simp2d
    #
    @6
    @9
    @8
    @13
    @14
    simp1d
    #
    @6
    @12
    @10
    cr
    @6
    @0
    @9
    @8
    @12
    @10
    wceq
    @0
    @5
    simpl
    @16
    @15
    @3
    @4
    cD
    cX
    xmetsym
    syl3anc
    @6
    @9
    @8
    @13
    @14
    simp3d
    #
    eqeltrrd
    @0
    @7
    @8
    @9
    @11
    w3a
    wb
    @5
    @4
    @3
    cD
    c.sm
    cX
    xmeter.1
    xmeterval
    adantr
    mpbir3and
    @0
    @5
    @4
    vz
    cv
    #
    c.sm
    wbr
    #
    wa
    #
    wa
    #
    @3
    @18
    c.sm
    wbr
    #
    @9
    @18
    cX
    wcel
    #
    @3
    @18
    cD
    co
    #
    cr
    wcel
    #
    @0
    @5
    @9
    @19
    @16
    adantrr
    #
    @21
    @8
    @23
    @4
    @18
    cD
    co
    #
    cr
    wcel
    #
    @0
    @19
    @8
    @23
    @28
    w3a
    #
    @5
    @0
    @19
    @29
    @4
    @18
    cD
    c.sm
    cX
    xmeter.1
    xmeterval
    biimpa
    adantrl
    #
    simp2d
    #
    @21
    @0
    @9
    @23
    @12
    @27
    cxad
    co
    #
    cr
    wcel
    #
    @24
    @32
    cle
    wbr
    #
    @25
    @0
    @20
    simpl
    #
    @26
    @31
    @21
    @13
    @28
    @33
    @0
    @5
    @13
    @19
    @17
    adantrr
    @21
    @8
    @23
    @28
    @30
    simp3d
    @13
    @28
    wa
    @32
    @12
    @27
    caddc
    co
    cr
    @12
    @27
    rexadd
    @12
    @27
    readdcl
    eqeltrd
    syl2anc
    @21
    @0
    @9
    @23
    @8
    @34
    @35
    @26
    @31
    @0
    @5
    @8
    @19
    @15
    adantrr
    @3
    @18
    @4
    cD
    cX
    xmettri
    syl13anc
    @3
    @18
    @32
    cD
    cX
    xmetlecl
    syl122anc
    @0
    @22
    @9
    @23
    @25
    w3a
    wb
    @20
    @3
    @18
    cD
    c.sm
    cX
    xmeter.1
    xmeterval
    adantr
    mpbir3and
    @0
    @9
    @9
    @9
    @3
    @3
    cD
    co
    #
    cr
    wcel
    #
    w3a
    #
    @3
    @3
    c.sm
    wbr
    @0
    @9
    @37
    @9
    wa
    #
    @38
    @0
    @9
    @37
    @0
    @9
    @37
    @0
    @9
    wa
    @36
    cc0
    cr
    @3
    cD
    cX
    xmet0
    0re
    syl6eqel
    ex
    pm4.71rd
    @38
    @9
    @9
    wa
    #
    @37
    wa
    @39
    @9
    @9
    @37
    df-3an
    @40
    @9
    @37
    @9
    anidm
    anbi2ci
    bitri
    syl6bbr
    @3
    @3
    cD
    c.sm
    cX
    xmeter.1
    xmeterval
    bitr4d
    iserd
end
