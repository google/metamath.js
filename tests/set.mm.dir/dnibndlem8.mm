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
include "simpl.mm"
include "readdcld.mm"
include "syl.mm"
include "reflcl.mm"
include "resubcld.mm"
include "dnicld1.mm"
include "leabsd.mm"
include "recnd.mm"
include "abssubd.mm"
include "breqtrd.mm"
include "lesub2dd.mm"
include "subsub3d.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem dnibndlem8
  let wph: wff ph
  let cA: class A
  assume dnibndlem8.1: |- ( ph -> A e. RR )


  assert |- ( ph -> ( ( 1 / 2 ) - ( abs ` ( ( |_ ` ( A + ( 1 / 2 ) ) ) - A ) ) ) <_ ( ( ( |_ ` ( A + ( 1 / 2 ) ) ) + ( 1 / 2 ) ) - A ) )

  proof
    wph
    c1
    c2
    cdiv
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
    cA
    cmin
    co
    cabs
    cfv
    #
    cmin
    co
    @0
    cA
    @2
    cmin
    co
    #
    cmin
    co
    #
    @2
    @0
    caddc
    co
    #
    cA
    cmin
    co
    #
    cle
    wph
    @4
    @3
    @0
    wph
    cA
    @2
    dnibndlem8.1
    wph
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    wph
    cA
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    wa
    #
    @8
    wph
    @9
    @10
    dnibndlem8.1
    @10
    wph
    halfre
    a1i
    #
    jca
    @11
    cA
    @0
    @9
    @10
    simpl
    @10
    @11
    halfre
    a1i
    readdcld
    syl
    @1
    reflcl
    syl
    #
    resubcld
    #
    wph
    cA
    dnibndlem8.1
    dnicld1
    @12
    wph
    @4
    @4
    cabs
    cfv
    @3
    cle
    wph
    @4
    @14
    leabsd
    wph
    cA
    @2
    wph
    cA
    dnibndlem8.1
    recnd
    #
    wph
    @2
    @13
    recnd
    #
    abssubd
    breqtrd
    lesub2dd
    wph
    @5
    @0
    @2
    caddc
    co
    #
    cA
    cmin
    co
    @7
    wph
    @0
    cA
    @2
    wph
    @0
    @12
    recnd
    #
    @15
    @16
    subsub3d
    wph
    @17
    @6
    cA
    cmin
    wph
    @0
    @2
    @18
    @16
    addcomd
    oveq1d
    eqtrd
    breqtrd
end
