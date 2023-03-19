include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "cneg.mm"
include "wa.mm"
include "dnicld1.mm"
include "resubcld.mm"
include "cr.mm"
include "wcel.mm"
include "halfre.mm"
include "a1i.mm"
include "recnd.mm"
include "negsubdi2d.mm"
include "cc0.mm"
include "readdcld.mm"
include "reflcl.mm"
include "syl.mm"
include "subcld.mm"
include "absge0d.mm"
include "subge02d.mm"
include "mpbid.mm"
include "rddif.mm"
include "letrd.mm"
include "eqbrtrd.mm"
include "lenegcon1d.mm"
include "jca.mm"
include "absled.mm"
include "mpbird.mm"

theorem dnibndlem11
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume dnibndlem11.1: |- ( ph -> A e. RR )
  assume dnibndlem11.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( abs ` ( ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) - ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) ) <_ ( 1 / 2 ) )

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
    #
    cfl
    cfv
    #
    cB
    cmin
    co
    #
    cabs
    cfv
    #
    cA
    @0
    caddc
    co
    #
    cfl
    cfv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    @0
    cle
    wbr
    @0
    cneg
    @9
    cle
    wbr
    #
    @9
    @0
    cle
    wbr
    #
    wa
    wph
    @10
    @11
    wph
    @9
    @0
    wph
    @4
    @8
    wph
    cB
    dnibndlem11.2
    dnicld1
    #
    wph
    cA
    dnibndlem11.1
    dnicld1
    #
    resubcld
    #
    @0
    cr
    wcel
    wph
    halfre
    a1i
    #
    wph
    @9
    cneg
    @8
    @4
    cmin
    co
    #
    @0
    cle
    wph
    @4
    @8
    wph
    @4
    @12
    recnd
    wph
    @8
    @13
    recnd
    negsubdi2d
    wph
    @16
    @8
    @0
    wph
    @8
    @4
    @13
    @12
    resubcld
    @13
    @15
    wph
    cc0
    @4
    cle
    wbr
    @16
    @8
    cle
    wbr
    wph
    @3
    wph
    @2
    cB
    wph
    @2
    wph
    @1
    cr
    wcel
    @2
    cr
    wcel
    wph
    cB
    @0
    dnibndlem11.2
    @15
    readdcld
    @1
    reflcl
    syl
    recnd
    wph
    cB
    dnibndlem11.2
    recnd
    subcld
    absge0d
    wph
    @8
    @4
    @13
    @12
    subge02d
    mpbid
    wph
    cA
    cr
    wcel
    @8
    @0
    cle
    wbr
    dnibndlem11.1
    cA
    rddif
    syl
    letrd
    eqbrtrd
    lenegcon1d
    wph
    @9
    @4
    @0
    @14
    @12
    @15
    wph
    cc0
    @8
    cle
    wbr
    @9
    @4
    cle
    wbr
    wph
    @7
    wph
    @6
    cA
    wph
    @6
    wph
    @5
    cr
    wcel
    @6
    cr
    wcel
    wph
    cA
    @0
    dnibndlem11.1
    @15
    readdcld
    @5
    reflcl
    syl
    recnd
    wph
    cA
    dnibndlem11.1
    recnd
    subcld
    absge0d
    wph
    @4
    @8
    @12
    @13
    subge02d
    mpbid
    wph
    cB
    cr
    wcel
    @4
    @0
    cle
    wbr
    dnibndlem11.2
    cB
    rddif
    syl
    letrd
    jca
    wph
    @9
    @0
    @14
    @15
    absled
    mpbird
end
