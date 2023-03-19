include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "1red.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "halfre.mm"
include "a1i.mm"
include "readdcld.mm"
include "reflcl.mm"
include "syl.mm"
include "jca.mm"
include "resubcl.mm"
include "resubcld.mm"
include "cle.mm"
include "recnd.mm"
include "2cnd.mm"
include "addsubassd.mm"
include "oveq1d.mm"
include "subcld.mm"
include "pnpcand.mm"
include "subsub4d.mm"
include "wceq.mm"
include "cc.mm"
include "ax-1cn.mm"
include "2halves.mm"
include "ax-mp.mm"
include "oveq2d.mm"
include "2m1e1.mm"
include "3eqtrd.mm"
include "eqcomd.mm"
include "2re.mm"
include "lesub1dd.mm"
include "eqbrtrd.mm"
include "wbr.mm"
include "flle.mm"
include "lesubaddd.mm"
include "mpbird.mm"
include "fllep1.mm"
include "addassd.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "leadd1d.mm"
include "le2subd.mm"
include "letrd.mm"

theorem dnibndlem10
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume dnibndlem10.1: |- ( ph -> A e. RR )
  assume dnibndlem10.2: |- ( ph -> B e. RR )
  assume dnibndlem10.3: |- ( ph -> ( ( |_ ` ( A + ( 1 / 2 ) ) ) + 2 ) <_ ( |_ ` ( B + ( 1 / 2 ) ) ) )


  assert |- ( ph -> 1 <_ ( B - A ) )

  proof
    wph
    c1
    cB
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @0
    cmin
    co
    #
    cA
    @0
    caddc
    co
    #
    cfl
    cfv
    #
    @0
    caddc
    co
    #
    cmin
    co
    #
    cB
    cA
    cmin
    co
    wph
    1red
    wph
    @3
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    wa
    @7
    cr
    wcel
    wph
    @8
    @9
    wph
    @2
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    wa
    @8
    wph
    @10
    @11
    wph
    @1
    cr
    wcel
    #
    @10
    wph
    cB
    @0
    dnibndlem10.2
    @11
    wph
    halfre
    a1i
    #
    readdcld
    #
    @1
    reflcl
    syl
    #
    @13
    jca
    @2
    @0
    resubcl
    syl
    #
    wph
    @5
    @0
    wph
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    wph
    cA
    @0
    dnibndlem10.1
    @13
    readdcld
    #
    @4
    reflcl
    syl
    #
    @13
    readdcld
    #
    jca
    @3
    @6
    resubcl
    syl
    wph
    cB
    cA
    dnibndlem10.2
    dnibndlem10.1
    resubcld
    wph
    c1
    @5
    c2
    caddc
    co
    #
    @0
    cmin
    co
    #
    @6
    cmin
    co
    #
    @7
    cle
    wph
    @23
    c1
    wph
    @23
    @5
    c2
    @0
    cmin
    co
    #
    caddc
    co
    #
    @6
    cmin
    co
    @24
    @0
    cmin
    co
    #
    c1
    wph
    @22
    @25
    @6
    cmin
    wph
    @5
    c2
    @0
    wph
    @5
    @19
    recnd
    #
    wph
    2cnd
    #
    wph
    @0
    @13
    recnd
    #
    addsubassd
    oveq1d
    wph
    @5
    @24
    @0
    @27
    wph
    c2
    @0
    @28
    @29
    subcld
    @29
    pnpcand
    wph
    @26
    c2
    @0
    @0
    caddc
    co
    #
    cmin
    co
    c2
    c1
    cmin
    co
    #
    c1
    wph
    c2
    @0
    @0
    @28
    @29
    @29
    subsub4d
    wph
    @30
    c1
    c2
    cmin
    @30
    c1
    wceq
    #
    wph
    c1
    cc
    wcel
    @32
    ax-1cn
    c1
    2halves
    ax-mp
    a1i
    #
    oveq2d
    @31
    c1
    wceq
    wph
    2m1e1
    a1i
    3eqtrd
    3eqtrd
    eqcomd
    wph
    @22
    @3
    @6
    wph
    @21
    cr
    wcel
    #
    @11
    wa
    @22
    cr
    wcel
    wph
    @34
    @11
    wph
    @5
    c2
    @19
    c2
    cr
    wcel
    wph
    2re
    a1i
    readdcld
    #
    @13
    jca
    @21
    @0
    resubcl
    syl
    @16
    @20
    wph
    @21
    @2
    @0
    @35
    @15
    @13
    dnibndlem10.3
    lesub1dd
    lesub1dd
    eqbrtrd
    wph
    @3
    cA
    cB
    @6
    @16
    dnibndlem10.1
    dnibndlem10.2
    @20
    wph
    @3
    cB
    cle
    wbr
    @2
    @1
    cle
    wbr
    #
    wph
    @12
    @36
    @14
    @1
    flle
    syl
    wph
    @2
    @0
    cB
    @15
    @13
    dnibndlem10.2
    lesubaddd
    mpbird
    wph
    cA
    @6
    cle
    wbr
    @4
    @6
    @0
    caddc
    co
    #
    cle
    wbr
    wph
    @4
    @5
    c1
    caddc
    co
    #
    @37
    cle
    wph
    @17
    @4
    @38
    cle
    wbr
    @18
    @4
    fllep1
    syl
    wph
    @37
    @38
    wph
    @37
    @5
    @30
    caddc
    co
    @38
    wph
    @5
    @0
    @0
    @27
    @29
    @29
    addassd
    wph
    @30
    c1
    @5
    caddc
    @33
    oveq2d
    eqtrd
    eqcomd
    breqtrd
    wph
    cA
    @6
    @0
    dnibndlem10.1
    @20
    @13
    leadd1d
    mpbird
    le2subd
    letrd
end
