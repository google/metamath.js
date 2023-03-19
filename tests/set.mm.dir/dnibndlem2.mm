include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cfl.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "halfre.mm"
include "a1i.mm"
include "jca.mm"
include "readdcl.mm"
include "syl.mm"
include "reflcl.mm"
include "recnd.mm"
include "subcld.mm"
include "abscld.mm"
include "cc.mm"
include "eqeltrrd.mm"
include "abs2difabsd.mm"
include "nnncan1d.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "abssubd.mm"
include "3eqtrd.mm"
include "leidd.mm"
include "eqbrtrrd.mm"
include "letrd.mm"
include "dnibndlem1.mm"
include "mpbird.mm"

theorem dnibndlem2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  assume dnibndlem2.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnibndlem2.2: |- ( ph -> A e. RR )
  assume dnibndlem2.3: |- ( ph -> B e. RR )
  assume dnibndlem2.4: |- ( ph -> ( |_ ` ( B + ( 1 / 2 ) ) ) = ( |_ ` ( A + ( 1 / 2 ) ) ) )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) ) <_ ( abs ` ( B - A ) ) )

  proof
    wph
    cB
    cT
    cfv
    cA
    cT
    cfv
    cmin
    co
    cabs
    cfv
    cB
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
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
    @2
    caddc
    co
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
    #
    @1
    cle
    wbr
    wph
    @11
    @5
    @8
    cmin
    co
    #
    cabs
    cfv
    #
    @1
    wph
    @10
    wph
    @6
    @9
    wph
    @6
    wph
    @5
    wph
    @4
    cB
    wph
    @4
    wph
    @3
    cr
    wcel
    #
    @4
    cr
    wcel
    wph
    cB
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    wa
    @14
    wph
    @15
    @16
    dnibndlem2.3
    @16
    wph
    halfre
    a1i
    jca
    cB
    @2
    readdcl
    syl
    @3
    reflcl
    syl
    recnd
    #
    wph
    cB
    dnibndlem2.3
    recnd
    #
    subcld
    #
    abscld
    recnd
    wph
    @9
    wph
    @8
    wph
    @7
    cA
    wph
    @4
    @7
    cc
    dnibndlem2.4
    @17
    eqeltrrd
    wph
    cA
    dnibndlem2.2
    recnd
    #
    subcld
    #
    abscld
    recnd
    subcld
    abscld
    wph
    @12
    wph
    @5
    @8
    @19
    @21
    subcld
    abscld
    wph
    @0
    wph
    cB
    cA
    @18
    @20
    subcld
    abscld
    #
    wph
    @5
    @8
    @19
    @21
    abs2difabsd
    wph
    @1
    @13
    @1
    cle
    wph
    @1
    @4
    cA
    cmin
    co
    #
    @5
    cmin
    co
    #
    cabs
    cfv
    @8
    @5
    cmin
    co
    #
    cabs
    cfv
    @13
    wph
    @0
    @24
    cabs
    wph
    @24
    @0
    wph
    @4
    cA
    cB
    @17
    @20
    @18
    nnncan1d
    eqcomd
    fveq2d
    wph
    @24
    @25
    cabs
    wph
    @23
    @8
    @5
    cmin
    wph
    @4
    @7
    cA
    cmin
    dnibndlem2.4
    oveq1d
    oveq1d
    fveq2d
    wph
    @8
    @5
    @21
    @19
    abssubd
    3eqtrd
    wph
    @1
    @22
    leidd
    eqbrtrrd
    letrd
    wph
    vx
    cA
    cB
    @1
    cT
    dnibndlem2.1
    dnibndlem2.2
    dnibndlem2.3
    dnibndlem1
    mpbird
end
