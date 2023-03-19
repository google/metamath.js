include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "clog.mm"
include "cmin.mm"
include "cc.mm"
include "cpi.mm"
include "cneg.mm"
include "cim.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "crn.mm"
include "ax-1cn.mm"
include "ax-icn.mm"
include "atandm2.mm"
include "simp1bi.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcl.mm"
include "simp3bi.mm"
include "logcld.mm"
include "subcl.mm"
include "simp2bi.mm"
include "subcld.mm"
include "adantr.mm"
include "cioo.mm"
include "wo.mm"
include "cr.mm"
include "wb.mm"
include "recld.mm"
include "0re.mm"
include "lttri2.mm"
include "sylancl.mm"
include "biimpa.mm"
include "wceq.mm"
include "imnegd.mm"
include "negsubdi2d.mm"
include "mulneg2.mm"
include "oveq2d.mm"
include "negsub.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "subneg.mm"
include "oveq12d.mm"
include "eqtr4d.mm"
include "eqtr3d.mm"
include "atandmneg.mm"
include "lt0neg1d.mm"
include "renegd.mm"
include "breqtrrd.mm"
include "atanlogsublem.mm"
include "syl2anc.mm"
include "picn.mm"
include "negnegi.mm"
include "oveq2i.mm"
include "syl6eleqr.mm"
include "eqeltrd.mm"
include "pire.mm"
include "renegcli.mm"
include "a1i.mm"
include "imcld.mm"
include "iooneg.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "jaodan.mm"
include "syldan.mm"
include "eliooord.mm"
include "syl.mm"
include "simpld.mm"
include "simprd.mm"
include "wi.mm"
include "ltle.mm"
include "mpd.mm"
include "ellogrn.mm"
include "syl3anbrc.mm"

theorem atanlogsub
  let cA: class A


  assert |- ( ( A e. dom arctan /\ ( Re ` A ) =/= 0 ) -> ( ( log ` ( 1 + ( _i x. A ) ) ) - ( log ` ( 1 - ( _i x. A ) ) ) ) e. ran log )

  proof
    cA
    catan
    cdm
    #
    wcel
    #
    cA
    cre
    cfv
    #
    cc0
    wne
    #
    wa
    #
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
    @5
    cmin
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cc
    wcel
    #
    cpi
    cneg
    #
    @10
    cim
    cfv
    #
    clt
    wbr
    #
    @13
    cpi
    cle
    wbr
    #
    @10
    clog
    crn
    wcel
    @1
    @11
    @3
    @1
    @7
    @9
    @1
    @6
    @1
    c1
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @6
    cc
    wcel
    ax-1cn
    @1
    ci
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @17
    ax-icn
    @1
    @19
    @8
    cc0
    wne
    #
    @6
    cc0
    wne
    #
    cA
    atandm2
    #
    simp1bi
    #
    ci
    cA
    mulcl
    sylancr
    #
    c1
    @5
    addcl
    sylancr
    @1
    @19
    @20
    @21
    @22
    simp3bi
    logcld
    #
    @1
    @8
    @1
    @16
    @17
    @8
    cc
    wcel
    ax-1cn
    @24
    c1
    @5
    subcl
    sylancr
    @1
    @19
    @20
    @21
    @22
    simp2bi
    logcld
    #
    subcld
    #
    adantr
    #
    @4
    @14
    @13
    cpi
    clt
    wbr
    #
    @4
    @13
    @12
    cpi
    cioo
    co
    #
    wcel
    #
    @14
    @29
    wa
    @1
    @3
    @2
    cc0
    clt
    wbr
    #
    cc0
    @2
    clt
    wbr
    #
    wo
    #
    @31
    @1
    @3
    @34
    @1
    @2
    cr
    wcel
    cc0
    cr
    wcel
    @3
    @34
    wb
    @1
    cA
    @23
    recld
    #
    0re
    @2
    cc0
    lttri2
    sylancl
    biimpa
    @1
    @32
    @31
    @33
    @1
    @32
    wa
    #
    @31
    @13
    cneg
    #
    @12
    @12
    cneg
    #
    cioo
    co
    #
    wcel
    #
    @36
    @37
    c1
    ci
    cA
    cneg
    #
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
    @42
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
    @39
    @1
    @37
    @48
    wceq
    @32
    @1
    @10
    cneg
    #
    cim
    cfv
    @37
    @48
    @1
    @10
    @27
    imnegd
    @1
    @49
    @47
    cim
    @1
    @49
    @9
    @7
    cmin
    co
    @47
    @1
    @7
    @9
    @25
    @26
    negsubdi2d
    @1
    @44
    @9
    @46
    @7
    cmin
    @1
    @43
    @8
    clog
    @1
    @43
    c1
    @5
    cneg
    #
    caddc
    co
    #
    @8
    @1
    @42
    @50
    c1
    caddc
    @1
    @18
    @19
    @42
    @50
    wceq
    ax-icn
    @23
    ci
    cA
    mulneg2
    sylancr
    #
    oveq2d
    @1
    @16
    @17
    @51
    @8
    wceq
    ax-1cn
    @24
    c1
    @5
    negsub
    sylancr
    eqtrd
    fveq2d
    @1
    @45
    @6
    clog
    @1
    @45
    c1
    @50
    cmin
    co
    #
    @6
    @1
    @42
    @50
    c1
    cmin
    @52
    oveq2d
    @1
    @16
    @17
    @53
    @6
    wceq
    ax-1cn
    @24
    c1
    @5
    subneg
    sylancr
    eqtrd
    fveq2d
    oveq12d
    eqtr4d
    fveq2d
    eqtr3d
    adantr
    @36
    @48
    @30
    @39
    @36
    @41
    @0
    wcel
    #
    cc0
    @41
    cre
    cfv
    #
    clt
    wbr
    @48
    @30
    wcel
    @1
    @54
    @32
    cA
    atandmneg
    adantr
    @36
    cc0
    @2
    cneg
    #
    @55
    clt
    @1
    @32
    cc0
    @56
    clt
    wbr
    @1
    @2
    @35
    lt0neg1d
    biimpa
    @36
    cA
    @1
    @19
    @32
    @23
    adantr
    renegd
    breqtrrd
    @41
    atanlogsublem
    syl2anc
    @38
    cpi
    @12
    cioo
    cpi
    picn
    negnegi
    oveq2i
    syl6eleqr
    eqeltrd
    @36
    @12
    cr
    wcel
    #
    cpi
    cr
    wcel
    #
    @13
    cr
    wcel
    #
    @31
    @40
    wb
    @57
    @36
    cpi
    pire
    renegcli
    a1i
    @58
    @36
    pire
    a1i
    @36
    @10
    @1
    @11
    @32
    @27
    adantr
    imcld
    @12
    cpi
    @13
    iooneg
    syl3anc
    mpbird
    cA
    atanlogsublem
    jaodan
    syldan
    @13
    @12
    cpi
    eliooord
    syl
    #
    simpld
    @4
    @29
    @15
    @4
    @14
    @29
    @60
    simprd
    @4
    @59
    @58
    @29
    @15
    wi
    @4
    @10
    @28
    imcld
    pire
    @13
    cpi
    ltle
    sylancl
    mpd
    @10
    ellogrn
    syl3anbrc
end
