include "ccj.mm"
include "cfv.mm"
include "caddc.mm"
include "co.mm"
include "cabs.mm"
include "cdiv.mm"
include "c2.mm"
include "clog.mm"
include "cim.mm"
include "ccos.mm"
include "cre.mm"
include "cjcld.mm"
include "addcld.mm"
include "abscld.mm"
include "recnd.mm"
include "2cnd.mm"
include "absne0d.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "a1i.mm"
include "divdiv32d.mm"
include "ci.mm"
include "cmul.mm"
include "ce.mm"
include "cneg.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "logcld.mm"
include "imcld.mm"
include "cosval.mm"
include "syl.mm"
include "efiarg.mm"
include "syl2anc.mm"
include "ax-icn.mm"
include "mulcld.mm"
include "efcj.mm"
include "cjmuld.mm"
include "cji.mm"
include "cjred.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "3eqtr3d.mm"
include "cjdivd.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "divdird.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "reval.mm"
include "3eqtr4d.mm"

theorem cosargd
  let wph: wff ph
  let cX: class X
  assume cosargd.1: |- ( ph -> X e. CC )
  assume cosargd.2: |- ( ph -> X =/= 0 )


  assert |- ( ph -> ( cos ` ( Im ` ( log ` X ) ) ) = ( ( Re ` X ) / ( abs ` X ) ) )

  proof
    wph
    cX
    cX
    ccj
    cfv
    #
    caddc
    co
    #
    cX
    cabs
    cfv
    #
    cdiv
    co
    #
    c2
    cdiv
    co
    #
    @1
    c2
    cdiv
    co
    #
    @2
    cdiv
    co
    cX
    clog
    cfv
    #
    cim
    cfv
    #
    ccos
    cfv
    #
    cX
    cre
    cfv
    #
    @2
    cdiv
    co
    wph
    @1
    @2
    c2
    wph
    cX
    @0
    cosargd.1
    wph
    cX
    cosargd.1
    cjcld
    #
    addcld
    wph
    @2
    wph
    cX
    cosargd.1
    abscld
    #
    recnd
    #
    wph
    2cnd
    wph
    cX
    cosargd.1
    cosargd.2
    absne0d
    #
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    divdiv32d
    wph
    @8
    ci
    @7
    cmul
    co
    #
    ce
    cfv
    #
    ci
    cneg
    #
    @7
    cmul
    co
    #
    ce
    cfv
    #
    caddc
    co
    #
    c2
    cdiv
    co
    #
    @4
    wph
    @7
    cc
    wcel
    @8
    @20
    wceq
    wph
    @7
    wph
    @6
    wph
    cX
    cosargd.1
    cosargd.2
    logcld
    imcld
    #
    recnd
    #
    @7
    cosval
    syl
    wph
    @19
    @3
    c2
    cdiv
    wph
    @19
    cX
    @2
    cdiv
    co
    #
    @0
    @2
    cdiv
    co
    #
    caddc
    co
    @3
    wph
    @15
    @23
    @18
    @24
    caddc
    wph
    cX
    cc
    wcel
    #
    cX
    cc0
    wne
    @15
    @23
    wceq
    cosargd.1
    cosargd.2
    cX
    efiarg
    syl2anc
    #
    wph
    @18
    @23
    ccj
    cfv
    #
    @0
    @2
    ccj
    cfv
    #
    cdiv
    co
    @24
    wph
    @14
    ccj
    cfv
    #
    ce
    cfv
    #
    @15
    ccj
    cfv
    #
    @18
    @27
    wph
    @14
    cc
    wcel
    @30
    @31
    wceq
    wph
    ci
    @7
    ci
    cc
    wcel
    wph
    ax-icn
    a1i
    #
    @22
    mulcld
    @14
    efcj
    syl
    wph
    @29
    @17
    ce
    wph
    @29
    ci
    ccj
    cfv
    #
    @7
    ccj
    cfv
    #
    cmul
    co
    @17
    wph
    ci
    @7
    @32
    @22
    cjmuld
    wph
    @33
    @16
    @34
    @7
    cmul
    @33
    @16
    wceq
    wph
    cji
    a1i
    wph
    @7
    @21
    cjred
    oveq12d
    eqtrd
    fveq2d
    wph
    @15
    @23
    ccj
    @26
    fveq2d
    3eqtr3d
    wph
    cX
    @2
    cosargd.1
    @12
    @13
    cjdivd
    wph
    @28
    @2
    @0
    cdiv
    wph
    @2
    @11
    cjred
    oveq2d
    3eqtrd
    oveq12d
    wph
    cX
    @0
    @2
    cosargd.1
    @10
    @12
    @13
    divdird
    eqtr4d
    oveq1d
    eqtrd
    wph
    @9
    @5
    @2
    cdiv
    wph
    @25
    @9
    @5
    wceq
    cosargd.1
    cX
    reval
    syl
    oveq1d
    3eqtr4d
end
