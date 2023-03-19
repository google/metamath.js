include "cmin.mm"
include "co.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cfl.mm"
include "cfv.mm"
include "cabs.mm"
include "cc.mm"
include "wcel.mm"
include "w3a.mm"
include "wceq.mm"
include "recnd.mm"
include "cr.mm"
include "wa.mm"
include "halfre.mm"
include "a1i.mm"
include "jca.mm"
include "readdcl.mm"
include "syl.mm"
include "reflcl.mm"
include "halfcn.mm"
include "subcld.mm"
include "3jca.mm"
include "npncan.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "1cnd.mm"
include "addsubass.mm"
include "1mhlfehlf.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "eqtrd.mm"
include "fveq2d.mm"

theorem dnibndlem3
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  assume dnibndlem3.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnibndlem3.2: |- ( ph -> A e. RR )
  assume dnibndlem3.3: |- ( ph -> B e. RR )
  assume dnibndlem3.4: |- ( ph -> ( |_ ` ( B + ( 1 / 2 ) ) ) = ( ( |_ ` ( A + ( 1 / 2 ) ) ) + 1 ) )


  assert |- ( ph -> ( abs ` ( B - A ) ) = ( abs ` ( ( B - ( ( |_ ` ( B + ( 1 / 2 ) ) ) - ( 1 / 2 ) ) ) + ( ( ( |_ ` ( A + ( 1 / 2 ) ) ) + ( 1 / 2 ) ) - A ) ) ) )

  proof
    wph
    cB
    cA
    cmin
    co
    #
    cB
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
    @1
    cmin
    co
    #
    cmin
    co
    #
    cA
    @1
    caddc
    co
    #
    cfl
    cfv
    #
    @1
    caddc
    co
    #
    cA
    cmin
    co
    #
    caddc
    co
    #
    cabs
    wph
    @0
    @5
    @4
    cA
    cmin
    co
    #
    caddc
    co
    #
    @10
    wph
    @12
    @0
    wph
    cB
    cc
    wcel
    #
    @4
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    w3a
    @12
    @0
    wceq
    wph
    @13
    @14
    @15
    wph
    cB
    dnibndlem3.3
    recnd
    wph
    @3
    @1
    wph
    @3
    wph
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    wph
    cB
    cr
    wcel
    #
    @1
    cr
    wcel
    #
    wa
    @16
    wph
    @17
    @18
    dnibndlem3.3
    @18
    wph
    halfre
    a1i
    #
    jca
    cB
    @1
    readdcl
    syl
    @2
    reflcl
    syl
    recnd
    @1
    cc
    wcel
    #
    wph
    halfcn
    a1i
    #
    subcld
    wph
    cA
    dnibndlem3.2
    recnd
    3jca
    cB
    @4
    cA
    npncan
    syl
    eqcomd
    wph
    @11
    @9
    @5
    caddc
    wph
    @4
    @8
    cA
    cmin
    wph
    @4
    @7
    c1
    caddc
    co
    #
    @1
    cmin
    co
    #
    @7
    c1
    @1
    cmin
    co
    #
    caddc
    co
    #
    @8
    wph
    @3
    @22
    @1
    cmin
    dnibndlem3.4
    oveq1d
    wph
    @7
    cc
    wcel
    #
    c1
    cc
    wcel
    #
    @20
    w3a
    @23
    @25
    wceq
    wph
    @26
    @27
    @20
    wph
    @7
    wph
    @6
    cr
    wcel
    #
    @7
    cr
    wcel
    wph
    cA
    cr
    wcel
    #
    @18
    wa
    @28
    wph
    @29
    @18
    dnibndlem3.2
    @19
    jca
    cA
    @1
    readdcl
    syl
    @6
    reflcl
    syl
    recnd
    wph
    1cnd
    @21
    3jca
    @7
    c1
    @1
    addsubass
    syl
    wph
    @24
    @1
    @7
    caddc
    @24
    @1
    wceq
    wph
    1mhlfehlf
    a1i
    oveq2d
    3eqtrd
    oveq1d
    oveq2d
    eqtrd
    fveq2d
end
