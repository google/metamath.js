include "crp.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdiv.mm"
include "cc0.mm"
include "cioo.mm"
include "wa.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "simpr.mm"
include "rpred.mm"
include "1rp.mm"
include "a1i.mm"
include "rpaddcld.mm"
include "rerpdivcld.mm"
include "cmin.mm"
include "rprecred.mm"
include "1red.mm"
include "0red.mm"
include "readdcld.mm"
include "ltaddrpd.mm"
include "recgt1i.mm"
include "syl2anc.mm"
include "simprd.mm"
include "1m0e1.mm"
include "syl6breqr.mm"
include "ltsub13d.mm"
include "wceq.mm"
include "1cnd.mm"
include "addcld.mm"
include "cneg.mm"
include "negcld.mm"
include "addneintrd.mm"
include "1pneg1e0.mm"
include "neeqtrd.mm"
include "divsubdird.mm"
include "pncan2d.mm"
include "oveq1d.mm"
include "dividd.mm"
include "3eqtr3d.mm"
include "adantr.mm"
include "breqtrrd.mm"
include "1m1e0.mm"
include "simpld.mm"
include "syl5eqbr.mm"
include "ltsub23d.mm"
include "eqbrtrd.mm"
include "cxr.mm"
include "w3a.mm"
include "wb.mm"
include "0xr.mm"
include "1re.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"
include "cc.mm"
include "wne.mm"
include "recrecd.mm"
include "pncand.mm"
include "sylib.mm"
include "simp1d.mm"
include "resubcld.mm"
include "eqeltrd.mm"
include "simp3d.mm"
include "elrpd.mm"
include "eqeltrrd.mm"
include "1p0e1.mm"
include "simp2d.mm"
include "reclt1d.mm"
include "mpbid.mm"
include "breqtrd.mm"
include "ltadd2d.mm"
include "mpbird.mm"
include "impbida.mm"

theorem xov1plusxeqvd
  let wph: wff ph
  let cX: class X
  assume xov1plusxeqvd.1: |- ( ph -> X e. CC )
  assume xov1plusxeqvd.2: |- ( ph -> X =/= -u 1 )


  assert |- ( ph -> ( X e. RR+ <-> ( X / ( 1 + X ) ) e. ( 0 (,) 1 ) ) )

  proof
    wph
    cX
    crp
    wcel
    #
    cX
    c1
    cX
    caddc
    co
    #
    cdiv
    co
    #
    cc0
    c1
    cioo
    co
    wcel
    #
    wph
    @0
    wa
    #
    @2
    cr
    wcel
    #
    cc0
    @2
    clt
    wbr
    #
    @2
    c1
    clt
    wbr
    #
    @3
    @4
    cX
    @1
    @4
    cX
    wph
    @0
    simpr
    #
    rpred
    #
    @4
    c1
    cX
    c1
    crp
    wcel
    @4
    1rp
    a1i
    @8
    rpaddcld
    #
    rerpdivcld
    @4
    cc0
    c1
    c1
    @1
    cdiv
    co
    #
    cmin
    co
    #
    @2
    clt
    @4
    @11
    c1
    cc0
    @4
    @1
    @10
    rprecred
    #
    @4
    1red
    #
    @4
    0red
    @4
    @11
    c1
    c1
    cc0
    cmin
    co
    #
    clt
    @4
    cc0
    @11
    clt
    wbr
    #
    @11
    c1
    clt
    wbr
    #
    @4
    @1
    cr
    wcel
    c1
    @1
    clt
    wbr
    @16
    @17
    wa
    @4
    c1
    cX
    @14
    @9
    readdcld
    @4
    c1
    cX
    @14
    @8
    ltaddrpd
    @1
    recgt1i
    syl2anc
    #
    simprd
    1m0e1
    syl6breqr
    ltsub13d
    wph
    @2
    @12
    wceq
    @0
    wph
    @1
    c1
    cmin
    co
    #
    @1
    cdiv
    co
    @1
    @1
    cdiv
    co
    #
    @11
    cmin
    co
    @2
    @12
    wph
    @1
    c1
    @1
    wph
    c1
    cX
    wph
    1cnd
    #
    xov1plusxeqvd.1
    addcld
    #
    @21
    @22
    wph
    @1
    c1
    c1
    cneg
    #
    caddc
    co
    #
    cc0
    wph
    c1
    cX
    @23
    @21
    xov1plusxeqvd.1
    wph
    c1
    @21
    negcld
    xov1plusxeqvd.2
    addneintrd
    @24
    cc0
    wceq
    wph
    1pneg1e0
    a1i
    neeqtrd
    #
    divsubdird
    wph
    @19
    cX
    @1
    cdiv
    wph
    c1
    cX
    @21
    xov1plusxeqvd.1
    pncan2d
    #
    oveq1d
    wph
    @20
    c1
    @11
    cmin
    wph
    @1
    @22
    @25
    dividd
    #
    oveq1d
    3eqtr3d
    adantr
    #
    breqtrrd
    @4
    @2
    @12
    c1
    clt
    @28
    @4
    c1
    c1
    @11
    @14
    @14
    @13
    @4
    c1
    c1
    cmin
    co
    #
    cc0
    @11
    clt
    1m1e0
    @4
    @16
    @17
    @18
    simpld
    syl5eqbr
    ltsub23d
    eqbrtrd
    cc0
    cxr
    wcel
    c1
    cxr
    wcel
    @3
    @5
    @6
    @7
    w3a
    #
    wb
    0xr
    c1
    1re
    rexri
    cc0
    c1
    @2
    elioo2
    mp2an
    #
    syl3anbrc
    wph
    @3
    wa
    #
    cX
    @32
    @19
    cX
    cr
    wph
    @19
    cX
    wceq
    @3
    @26
    adantr
    @32
    @1
    c1
    @32
    c1
    @11
    cdiv
    co
    #
    @1
    cr
    @32
    @1
    wph
    @1
    cc
    wcel
    @3
    @22
    adantr
    wph
    @1
    cc0
    wne
    @3
    @25
    adantr
    recrecd
    #
    @32
    @11
    @32
    @11
    @32
    @11
    c1
    @2
    cmin
    co
    #
    cr
    wph
    @11
    @35
    wceq
    @3
    wph
    @1
    cX
    cmin
    co
    #
    @1
    cdiv
    co
    @20
    @2
    cmin
    co
    @11
    @35
    wph
    @1
    cX
    @1
    @22
    xov1plusxeqvd.1
    @22
    @25
    divsubdird
    wph
    @36
    c1
    @1
    cdiv
    wph
    c1
    cX
    @21
    xov1plusxeqvd.1
    pncand
    oveq1d
    wph
    @20
    c1
    @2
    cmin
    @27
    oveq1d
    3eqtr3d
    adantr
    #
    @32
    c1
    @2
    @32
    1red
    #
    @32
    @5
    @6
    @7
    @32
    @3
    @30
    wph
    @3
    simpr
    @31
    sylib
    #
    simp1d
    #
    resubcld
    eqeltrd
    @32
    cc0
    @35
    @11
    clt
    @32
    @2
    c1
    cc0
    @40
    @38
    @32
    0red
    #
    @32
    @2
    c1
    @15
    clt
    @32
    @5
    @6
    @7
    @39
    simp3d
    1m0e1
    syl6breqr
    ltsub13d
    @37
    breqtrrd
    elrpd
    #
    rprecred
    eqeltrrd
    @38
    resubcld
    eqeltrrd
    #
    @32
    cc0
    cX
    clt
    wbr
    c1
    cc0
    caddc
    co
    #
    @1
    clt
    wbr
    @32
    @44
    c1
    @1
    clt
    1p0e1
    @32
    c1
    @33
    @1
    clt
    @32
    @17
    c1
    @33
    clt
    wbr
    @32
    @11
    @35
    c1
    clt
    @37
    @32
    c1
    c1
    @2
    @38
    @38
    @40
    @32
    @29
    cc0
    @2
    clt
    1m1e0
    @32
    @5
    @6
    @7
    @39
    simp2d
    syl5eqbr
    ltsub23d
    eqbrtrd
    @32
    @11
    @42
    reclt1d
    mpbid
    @34
    breqtrd
    syl5eqbr
    @32
    cc0
    cX
    c1
    @41
    @43
    @38
    ltadd2d
    mpbird
    elrpd
    impbida
end
