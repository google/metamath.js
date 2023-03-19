include "cc.mm"
include "wcel.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "cfv.mm"
include "cneg.mm"
include "caddc.mm"
include "cmin.mm"
include "c2.mm"
include "cdiv.mm"
include "ccos.mm"
include "csin.mm"
include "wceq.mm"
include "ax-icn.mm"
include "mulcl.mm"
include "mpan.mm"
include "efcl.mm"
include "syl.mm"
include "negicn.mm"
include "addcld.mm"
include "subcld.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "2cn.mm"
include "2ne0.mm"
include "pm3.2i.mm"
include "divdir.mm"
include "mp3an3.mm"
include "syl2anc.mm"
include "pncan3d.mm"
include "oveq2d.mm"
include "addassd.mm"
include "2timesd.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "divcan3.mm"
include "mp3an23.mm"
include "eqtr2d.mm"
include "cosval.mm"
include "2mulicn.mm"
include "2muline0.mm"
include "div12.mm"
include "mp3an13.mm"
include "sinval.mm"
include "c1.mm"
include "divrec.mm"
include "mulid2i.mm"
include "oveq1i.mm"
include "ine0.mm"
include "dividi.mm"
include "oveq2i.mm"
include "ax-1cn.mm"
include "divmuldivi.mm"
include "eqtr3i.mm"
include "halfcn.mm"
include "mulid1i.mm"
include "syl6eqr.mm"
include "oveq12d.mm"

theorem efival
  let cA: class A


  assert |- ( A e. CC -> ( exp ` ( _i x. A ) ) = ( ( cos ` A ) + ( _i x. ( sin ` A ) ) ) )

  proof
    cA
    cc
    wcel
    #
    ci
    cA
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    cA
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    @2
    @5
    cmin
    co
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @6
    c2
    cdiv
    co
    #
    @7
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @2
    cA
    ccos
    cfv
    #
    ci
    cA
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    @0
    @6
    cc
    wcel
    #
    @7
    cc
    wcel
    #
    @9
    @12
    wceq
    #
    @0
    @2
    @5
    @0
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    ci
    cc
    wcel
    #
    @0
    @19
    ax-icn
    ci
    cA
    mulcl
    mpan
    @1
    efcl
    syl
    #
    @0
    @4
    cc
    wcel
    #
    @5
    cc
    wcel
    @3
    cc
    wcel
    @0
    @23
    negicn
    @3
    cA
    mulcl
    mpan
    @4
    efcl
    syl
    #
    addcld
    @0
    @2
    @5
    @22
    @24
    subcld
    #
    @16
    @17
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    wa
    @18
    @26
    @27
    2cn
    2ne0
    pm3.2i
    @6
    @7
    c2
    divdir
    mp3an3
    syl2anc
    @0
    @9
    c2
    @2
    cmul
    co
    #
    c2
    cdiv
    co
    #
    @2
    @0
    @8
    @28
    c2
    cdiv
    @0
    @2
    @5
    @7
    caddc
    co
    #
    caddc
    co
    @2
    @2
    caddc
    co
    @8
    @28
    @0
    @30
    @2
    @2
    caddc
    @0
    @5
    @2
    @24
    @22
    pncan3d
    oveq2d
    @0
    @2
    @5
    @7
    @22
    @24
    @25
    addassd
    @0
    @2
    @22
    2timesd
    3eqtr4d
    oveq1d
    @0
    @20
    @29
    @2
    wceq
    #
    @22
    @20
    @26
    @27
    @31
    2cn
    2ne0
    @2
    c2
    divcan3
    mp3an23
    syl
    eqtr2d
    @0
    @13
    @10
    @15
    @11
    caddc
    cA
    cosval
    @0
    ci
    @7
    c2
    ci
    cmul
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @7
    ci
    @32
    cdiv
    co
    #
    cmul
    co
    #
    @15
    @11
    @0
    @17
    @34
    @36
    wceq
    #
    @25
    @21
    @17
    @32
    cc
    wcel
    #
    @32
    cc0
    wne
    #
    wa
    @37
    ax-icn
    @38
    @39
    2mulicn
    2muline0
    pm3.2i
    ci
    @7
    @32
    div12
    mp3an13
    syl
    @0
    @14
    @33
    ci
    cmul
    cA
    sinval
    oveq2d
    @0
    @11
    @7
    c1
    c2
    cdiv
    co
    #
    cmul
    co
    #
    @36
    @0
    @17
    @11
    @41
    wceq
    #
    @25
    @17
    @26
    @27
    @42
    2cn
    2ne0
    @7
    c2
    divrec
    mp3an23
    syl
    @35
    @40
    @7
    cmul
    c1
    ci
    cmul
    co
    #
    @32
    cdiv
    co
    #
    @35
    @40
    @43
    ci
    @32
    cdiv
    ci
    ax-icn
    mulid2i
    oveq1i
    @40
    c1
    cmul
    co
    #
    @44
    @40
    @40
    ci
    ci
    cdiv
    co
    #
    cmul
    co
    @45
    @44
    @46
    c1
    @40
    cmul
    ci
    ax-icn
    ine0
    dividi
    oveq2i
    c1
    c2
    ci
    ci
    ax-1cn
    2cn
    ax-icn
    ax-icn
    2ne0
    ine0
    divmuldivi
    eqtr3i
    @40
    halfcn
    mulid1i
    eqtr3i
    eqtr3i
    oveq2i
    syl6eqr
    3eqtr4d
    oveq12d
    3eqtr4d
end
