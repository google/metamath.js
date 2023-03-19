include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "ccj.mm"
include "cmul.mm"
include "cre.mm"
include "cdiv.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "sqabssub.mm"
include "syl2anc.mm"
include "absdivd.mm"
include "oveq2d.mm"
include "abscld.mm"
include "remulcld.mm"
include "recnd.mm"
include "divcld.mm"
include "recld.mm"
include "absne0d.mm"
include "divne0d.mm"
include "div12d.mm"
include "eqtrd.mm"
include "divdiv2d.mm"
include "sqvald.mm"
include "oveq1d.mm"
include "mul31d.mm"
include "eqtr4d.mm"
include "sqcld.mm"
include "divcan4d.mm"
include "3eqtr2rd.mm"
include "mulcomd.mm"
include "resqcld.mm"
include "remul2d.mm"
include "c1.mm"
include "divrecd.mm"
include "cc0.mm"
include "wne.mm"
include "recval.mm"
include "cjcld.mm"
include "wb.mm"
include "sqne0.mm"
include "syl.mm"
include "mpbird.mm"
include "divcan2d.mm"
include "eqtr3d.mm"
include "fveq2d.mm"

theorem lawcoslem1
  let wph: wff ph
  let cU: class U
  let cV: class V
  assume lawcoslem1.1: |- ( ph -> U e. CC )
  assume lawcoslem1.2: |- ( ph -> V e. CC )
  assume lawcoslem1.3: |- ( ph -> U =/= 0 )
  assume lawcoslem1.4: |- ( ph -> V =/= 0 )


  assert |- ( ph -> ( ( abs ` ( U - V ) ) ^ 2 ) = ( ( ( ( abs ` U ) ^ 2 ) + ( ( abs ` V ) ^ 2 ) ) - ( 2 x. ( ( ( abs ` U ) x. ( abs ` V ) ) x. ( ( Re ` ( U / V ) ) / ( abs ` ( U / V ) ) ) ) ) ) )

  proof
    wph
    cU
    cV
    cmin
    co
    cabs
    cfv
    c2
    cexp
    co
    #
    cU
    cabs
    cfv
    #
    c2
    cexp
    co
    cV
    cabs
    cfv
    #
    c2
    cexp
    co
    #
    caddc
    co
    #
    c2
    cU
    cV
    ccj
    cfv
    #
    cmul
    co
    #
    cre
    cfv
    #
    cmul
    co
    #
    cmin
    co
    #
    @4
    c2
    @1
    @2
    cmul
    co
    #
    cU
    cV
    cdiv
    co
    #
    cre
    cfv
    #
    @11
    cabs
    cfv
    #
    cdiv
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cmin
    co
    wph
    cU
    cc
    wcel
    cV
    cc
    wcel
    #
    @0
    @9
    wceq
    lawcoslem1.1
    lawcoslem1.2
    cU
    cV
    sqabssub
    syl2anc
    wph
    @8
    @16
    @4
    cmin
    wph
    @7
    @15
    c2
    cmul
    wph
    @15
    @12
    @10
    @1
    @2
    cdiv
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @12
    @3
    cmul
    co
    #
    @7
    wph
    @15
    @10
    @12
    @18
    cdiv
    co
    #
    cmul
    co
    @20
    wph
    @14
    @22
    @10
    cmul
    wph
    @13
    @18
    @12
    cdiv
    wph
    cU
    cV
    lawcoslem1.1
    lawcoslem1.2
    lawcoslem1.4
    absdivd
    oveq2d
    oveq2d
    wph
    @10
    @12
    @18
    wph
    @10
    wph
    @1
    @2
    wph
    cU
    lawcoslem1.1
    abscld
    #
    wph
    cV
    lawcoslem1.2
    abscld
    #
    remulcld
    recnd
    #
    wph
    @12
    wph
    @11
    wph
    cU
    cV
    lawcoslem1.1
    lawcoslem1.2
    lawcoslem1.4
    divcld
    #
    recld
    recnd
    #
    wph
    @1
    @2
    wph
    @1
    @23
    recnd
    #
    wph
    @2
    @24
    recnd
    #
    wph
    cV
    lawcoslem1.2
    lawcoslem1.4
    absne0d
    #
    divcld
    wph
    @1
    @2
    @28
    @29
    wph
    cU
    lawcoslem1.1
    lawcoslem1.3
    absne0d
    #
    @30
    divne0d
    div12d
    eqtrd
    wph
    @3
    @19
    @12
    cmul
    wph
    @19
    @10
    @2
    cmul
    co
    #
    @1
    cdiv
    co
    @3
    @1
    cmul
    co
    #
    @1
    cdiv
    co
    @3
    wph
    @10
    @1
    @2
    @25
    @28
    @29
    @31
    @30
    divdiv2d
    wph
    @33
    @32
    @1
    cdiv
    wph
    @33
    @2
    @2
    cmul
    co
    #
    @1
    cmul
    co
    @32
    wph
    @3
    @34
    @1
    cmul
    wph
    @2
    @29
    sqvald
    oveq1d
    wph
    @1
    @2
    @2
    @28
    @29
    @29
    mul31d
    eqtr4d
    oveq1d
    wph
    @3
    @1
    wph
    @2
    @29
    sqcld
    #
    @28
    @31
    divcan4d
    3eqtr2rd
    oveq2d
    wph
    @21
    @3
    @11
    cmul
    co
    #
    cre
    cfv
    #
    @7
    wph
    @21
    @3
    @12
    cmul
    co
    @37
    wph
    @12
    @3
    @27
    @35
    mulcomd
    wph
    @3
    @11
    wph
    @2
    @24
    resqcld
    @26
    remul2d
    eqtr4d
    wph
    @36
    @6
    cre
    wph
    cU
    @3
    cV
    cdiv
    co
    #
    cmul
    co
    @36
    @6
    wph
    cU
    @3
    cV
    lawcoslem1.1
    @35
    lawcoslem1.2
    lawcoslem1.4
    div12d
    wph
    @38
    @5
    cU
    cmul
    wph
    @38
    @3
    c1
    cV
    cdiv
    co
    #
    cmul
    co
    #
    @5
    wph
    @3
    cV
    @35
    lawcoslem1.2
    lawcoslem1.4
    divrecd
    wph
    @40
    @3
    @5
    @3
    cdiv
    co
    #
    cmul
    co
    @5
    wph
    @39
    @41
    @3
    cmul
    wph
    @17
    cV
    cc0
    wne
    @39
    @41
    wceq
    lawcoslem1.2
    lawcoslem1.4
    cV
    recval
    syl2anc
    oveq2d
    wph
    @5
    @3
    wph
    cV
    lawcoslem1.2
    cjcld
    @35
    wph
    @3
    cc0
    wne
    #
    @2
    cc0
    wne
    #
    @30
    wph
    @2
    cc
    wcel
    @42
    @43
    wb
    @29
    @2
    sqne0
    syl
    mpbird
    divcan2d
    eqtrd
    eqtrd
    oveq2d
    eqtr3d
    fveq2d
    eqtrd
    3eqtr2rd
    oveq2d
    oveq2d
    eqtrd
end
