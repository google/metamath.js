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
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "halfre.mm"
include "a1i.mm"
include "jca.mm"
include "readdcl.mm"
include "syl.mm"
include "reflcl.mm"
include "resubcl.mm"
include "dnicld1.mm"
include "leabsd.mm"
include "lesub2dd.mm"
include "recnd.mm"
include "subsub3d.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "breqtrd.mm"

theorem dnibndlem7
  let wph: wff ph
  let cB: class B
  assume dnibndlem7.1: |- ( ph -> B e. RR )


  assert |- ( ph -> ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( B + ( 1 / 2 ) ) ) - B ) ) ) <_ ( B - ( ( |_ ` ( B + ( 1 / 2 ) ) ) - ( 1 / 2 ) ) ) )

  proof
    wph
    c1
    c2
    cdiv
    co
    #
    cB
    @0
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
    cmin
    co
    @0
    @3
    cmin
    co
    #
    cB
    @2
    @0
    cmin
    co
    cmin
    co
    #
    cle
    wph
    @3
    @4
    @0
    wph
    @2
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    @3
    cr
    wcel
    wph
    @7
    @8
    wph
    @1
    cr
    wcel
    #
    @7
    wph
    @8
    @0
    cr
    wcel
    #
    wa
    @9
    wph
    @8
    @10
    dnibndlem7.1
    @10
    wph
    halfre
    a1i
    #
    jca
    cB
    @0
    readdcl
    syl
    @1
    reflcl
    syl
    #
    dnibndlem7.1
    jca
    @2
    cB
    resubcl
    syl
    #
    wph
    cB
    dnibndlem7.1
    dnicld1
    @11
    wph
    @3
    @13
    leabsd
    lesub2dd
    wph
    @5
    @0
    cB
    caddc
    co
    #
    @2
    cmin
    co
    @1
    @2
    cmin
    co
    #
    @6
    wph
    @0
    @2
    cB
    wph
    @0
    @11
    recnd
    #
    wph
    @2
    @12
    recnd
    #
    wph
    cB
    dnibndlem7.1
    recnd
    #
    subsub3d
    wph
    @14
    @1
    @2
    cmin
    wph
    @0
    cB
    @16
    @18
    addcomd
    oveq1d
    wph
    @6
    @15
    wph
    cB
    @2
    @0
    @18
    @17
    @16
    subsub3d
    eqcomd
    3eqtrd
    breqtrd
end
