include "crp.mm"
include "wcel.mm"
include "catan.mm"
include "cfv.mm"
include "cr.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "cioo.mm"
include "rpre.mm"
include "atanrecl.mm"
include "syl.mm"
include "cc.mm"
include "cc0.mm"
include "wne.mm"
include "wceq.mm"
include "picn.mm"
include "2cn.mm"
include "2ne0.mm"
include "divneg.mm"
include "mp3an.mm"
include "cmul.mm"
include "wa.mm"
include "c1.mm"
include "ci.mm"
include "caddc.mm"
include "clog.mm"
include "cmin.mm"
include "cim.mm"
include "cre.mm"
include "ax-1cn.mm"
include "ax-icn.mm"
include "recnd.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcl.mm"
include "cdm.mm"
include "w3a.mm"
include "atanre.mm"
include "atandm2.mm"
include "sylib.mm"
include "simp3d.mm"
include "logcld.mm"
include "subcl.mm"
include "simp2d.mm"
include "subcld.mm"
include "imre.mm"
include "atanval.mm"
include "oveq2d.mm"
include "divcan2i.mm"
include "oveq1i.mm"
include "2re.mm"
include "a1i.mm"
include "halfcl.mm"
include "mp1i.mm"
include "mulassd.mm"
include "syl5eqr.mm"
include "eqtr4d.mm"
include "negsubdi2d.mm"
include "mulneg12.mm"
include "fveq2d.mm"
include "remulcl.mm"
include "rered.mm"
include "3eqtr2rd.mm"
include "rpgt0.mm"
include "breqtrrd.mm"
include "atanlogsublem.mm"
include "syl2anc.mm"
include "eqeltrd.mm"
include "eliooord.mm"
include "simpld.mm"
include "wb.mm"
include "pire.mm"
include "renegcli.mm"
include "2pos.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "syl5eqbr.mm"
include "simprd.mm"
include "ltmuldiv2.mm"
include "mpbid.mm"
include "cxr.mm"
include "halfpire.mm"
include "rexri.mm"
include "elioo2.mm"
include "mp2an.mm"
include "syl3anbrc.mm"

theorem atanbndlem
  let cA: class A


  assert |- ( A e. RR+ -> ( arctan ` A ) e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) )

  proof
    cA
    crp
    wcel
    #
    cA
    catan
    cfv
    #
    cr
    wcel
    #
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @1
    clt
    wbr
    #
    @1
    @3
    clt
    wbr
    #
    @1
    @4
    @3
    cioo
    co
    wcel
    #
    @0
    cA
    cr
    wcel
    #
    @2
    cA
    rpre
    #
    cA
    atanrecl
    syl
    #
    @0
    @4
    cpi
    cneg
    #
    c2
    cdiv
    co
    #
    @1
    clt
    cpi
    cc
    wcel
    c2
    cc
    wcel
    c2
    cc0
    wne
    @4
    @12
    wceq
    picn
    2cn
    2ne0
    cpi
    c2
    divneg
    mp3an
    @0
    @12
    @1
    clt
    wbr
    #
    @11
    c2
    @1
    cmul
    co
    #
    clt
    wbr
    #
    @0
    @15
    @14
    cpi
    clt
    wbr
    #
    @0
    @14
    @11
    cpi
    cioo
    co
    #
    wcel
    @15
    @16
    wa
    @0
    @14
    c1
    ci
    cA
    cmul
    co
    #
    caddc
    co
    #
    clog
    cfv
    #
    c1
    @18
    cmin
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cim
    cfv
    #
    @17
    @0
    @24
    ci
    cneg
    @23
    cmul
    co
    #
    cre
    cfv
    #
    @14
    cre
    cfv
    @14
    @0
    @23
    cc
    wcel
    #
    @24
    @26
    wceq
    @0
    @20
    @22
    @0
    @19
    @0
    c1
    cc
    wcel
    #
    @18
    cc
    wcel
    #
    @19
    cc
    wcel
    ax-1cn
    @0
    ci
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @29
    ax-icn
    @0
    cA
    @9
    recnd
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @18
    addcl
    sylancr
    @0
    @31
    @21
    cc0
    wne
    #
    @19
    cc0
    wne
    #
    @0
    cA
    catan
    cdm
    wcel
    #
    @31
    @33
    @34
    w3a
    @0
    @8
    @35
    @9
    cA
    atanre
    syl
    #
    cA
    atandm2
    sylib
    #
    simp3d
    logcld
    #
    @0
    @21
    @0
    @28
    @29
    @21
    cc
    wcel
    ax-1cn
    @32
    c1
    @18
    subcl
    sylancr
    @0
    @31
    @33
    @34
    @37
    simp2d
    logcld
    #
    subcld
    #
    @23
    imre
    syl
    @0
    @14
    @25
    cre
    @0
    @14
    ci
    @23
    cneg
    #
    cmul
    co
    #
    @25
    @0
    @14
    ci
    @22
    @20
    cmin
    co
    #
    cmul
    co
    #
    @42
    @0
    @14
    c2
    ci
    c2
    cdiv
    co
    #
    @43
    cmul
    co
    #
    cmul
    co
    #
    @44
    @0
    @1
    @46
    c2
    cmul
    @0
    @35
    @1
    @46
    wceq
    @36
    cA
    atanval
    syl
    oveq2d
    @0
    @44
    c2
    @45
    cmul
    co
    #
    @43
    cmul
    co
    @47
    @48
    ci
    @43
    cmul
    ci
    c2
    ax-icn
    2cn
    2ne0
    divcan2i
    oveq1i
    @0
    c2
    @45
    @43
    @0
    c2
    c2
    cr
    wcel
    #
    @0
    2re
    a1i
    #
    recnd
    @30
    @45
    cc
    wcel
    @0
    ax-icn
    ci
    halfcl
    mp1i
    @0
    @22
    @20
    @39
    @38
    subcld
    mulassd
    syl5eqr
    eqtr4d
    @0
    @41
    @43
    ci
    cmul
    @0
    @20
    @22
    @38
    @39
    negsubdi2d
    oveq2d
    eqtr4d
    @0
    @30
    @27
    @25
    @42
    wceq
    ax-icn
    @40
    ci
    @23
    mulneg12
    sylancr
    eqtr4d
    fveq2d
    @0
    @14
    @0
    @49
    @2
    @14
    cr
    wcel
    2re
    @10
    c2
    @1
    remulcl
    sylancr
    rered
    3eqtr2rd
    @0
    @35
    cc0
    cA
    cre
    cfv
    #
    clt
    wbr
    @24
    @17
    wcel
    @36
    @0
    cc0
    cA
    @51
    clt
    cA
    rpgt0
    @0
    cA
    @9
    rered
    breqtrrd
    cA
    atanlogsublem
    syl2anc
    eqeltrd
    @14
    @11
    cpi
    eliooord
    syl
    #
    simpld
    @0
    @11
    cr
    wcel
    #
    @2
    @49
    cc0
    c2
    clt
    wbr
    #
    @13
    @15
    wb
    @53
    @0
    cpi
    pire
    renegcli
    a1i
    @10
    @50
    @54
    @0
    2pos
    a1i
    #
    @11
    @1
    c2
    ltdivmul
    syl112anc
    mpbird
    syl5eqbr
    @0
    @16
    @6
    @0
    @15
    @16
    @52
    simprd
    @0
    @2
    cpi
    cr
    wcel
    #
    @49
    @54
    @16
    @6
    wb
    @10
    @56
    @0
    pire
    a1i
    @50
    @55
    @1
    cpi
    c2
    ltmuldiv2
    syl112anc
    mpbid
    @4
    cxr
    wcel
    @3
    cxr
    wcel
    @7
    @2
    @5
    @6
    w3a
    wb
    @4
    @3
    halfpire
    renegcli
    rexri
    @3
    halfpire
    rexri
    @4
    @3
    @1
    elioo2
    mp2an
    syl3anbrc
end
