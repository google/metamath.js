include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "dnicld1.mm"
include "recnd.mm"
include "subcld.mm"
include "abscld.mm"
include "cc.mm"
include "wcel.mm"
include "halfcn.mm"
include "a1i.mm"
include "readdcld.mm"
include "cr.mm"
include "wa.mm"
include "halfre.mm"
include "jca.mm"
include "resubcl.mm"
include "syl.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "3jca.mm"
include "abs3dif.mm"
include "abssubd.mm"
include "cc0.mm"
include "rddif2.mm"
include "absidd.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eqled.mm"
include "letrd.mm"

theorem dnibndlem6
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume dnibndlem6.1: |- ( ph -> A e. RR )
  assume dnibndlem6.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( abs ` ( ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) - ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) ) <_ ( ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) ) + ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) ) )

  proof
    wph
    cB
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    cfl
    cfv
    cB
    cmin
    co
    cabs
    cfv
    #
    cA
    @0
    caddc
    co
    cfl
    cfv
    cA
    cmin
    co
    cabs
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @1
    @0
    cmin
    co
    #
    cabs
    cfv
    #
    @0
    @2
    cmin
    co
    #
    cabs
    cfv
    #
    caddc
    co
    #
    @0
    @1
    cmin
    co
    #
    @7
    caddc
    co
    #
    wph
    @3
    wph
    @1
    @2
    wph
    @1
    wph
    cB
    dnibndlem6.2
    dnicld1
    #
    recnd
    #
    wph
    @2
    wph
    cA
    dnibndlem6.1
    dnicld1
    #
    recnd
    #
    subcld
    abscld
    wph
    @6
    @8
    wph
    @5
    wph
    @1
    @0
    @13
    @0
    cc
    wcel
    #
    wph
    halfcn
    a1i
    #
    subcld
    abscld
    wph
    @7
    wph
    @0
    @2
    @17
    @15
    subcld
    abscld
    readdcld
    #
    wph
    @10
    @7
    wph
    @0
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    @10
    cr
    wcel
    wph
    @19
    @20
    @19
    wph
    halfre
    a1i
    #
    @12
    jca
    @0
    @1
    resubcl
    syl
    #
    wph
    @19
    @2
    cr
    wcel
    #
    wa
    @7
    cr
    wcel
    wph
    @19
    @23
    @21
    @14
    jca
    @0
    @2
    resubcl
    syl
    #
    readdcld
    wph
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @16
    w3a
    @4
    @9
    cle
    wbr
    wph
    @25
    @26
    @16
    @13
    @15
    @17
    3jca
    @1
    @2
    @0
    abs3dif
    syl
    wph
    @9
    @11
    @18
    wph
    @6
    @10
    @8
    @7
    caddc
    wph
    @6
    @10
    cabs
    cfv
    @10
    wph
    @1
    @0
    @13
    @17
    abssubd
    wph
    @10
    @22
    wph
    cB
    cr
    wcel
    cc0
    @10
    cle
    wbr
    dnibndlem6.2
    cB
    rddif2
    syl
    absidd
    eqtrd
    wph
    @7
    @24
    wph
    cA
    cr
    wcel
    cc0
    @7
    cle
    wbr
    dnibndlem6.1
    cA
    rddif2
    syl
    absidd
    oveq12d
    eqled
    letrd
end
