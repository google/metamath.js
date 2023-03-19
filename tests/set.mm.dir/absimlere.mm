include "cmin.mm"
include "co.mm"
include "cim.mm"
include "cfv.mm"
include "cabs.mm"
include "cle.mm"
include "cc.mm"
include "wcel.mm"
include "wbr.mm"
include "recnd.mm"
include "subcld.mm"
include "absimle.mm"
include "syl.mm"
include "cc0.mm"
include "imsubd.mm"
include "reim0d.mm"
include "oveq2d.mm"
include "imcld.mm"
include "subid1d.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "abssubd.mm"
include "3brtr4d.mm"

theorem absimlere
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume absimlere.1: |- ( ph -> A e. CC )
  assume absimlere.2: |- ( ph -> B e. RR )


  assert |- ( ph -> ( abs ` ( Im ` A ) ) <_ ( abs ` ( B - A ) ) )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cim
    cfv
    #
    cabs
    cfv
    #
    @0
    cabs
    cfv
    #
    cA
    cim
    cfv
    #
    cabs
    cfv
    cB
    cA
    cmin
    co
    cabs
    cfv
    cle
    wph
    @0
    cc
    wcel
    @2
    @3
    cle
    wbr
    wph
    cA
    cB
    absimlere.1
    wph
    cB
    absimlere.2
    recnd
    #
    subcld
    @0
    absimle
    syl
    wph
    @4
    @1
    cabs
    wph
    @1
    @4
    cB
    cim
    cfv
    #
    cmin
    co
    @4
    cc0
    cmin
    co
    @4
    wph
    cA
    cB
    absimlere.1
    @5
    imsubd
    wph
    @6
    cc0
    @4
    cmin
    wph
    cB
    absimlere.2
    reim0d
    oveq2d
    wph
    @4
    wph
    @4
    wph
    cA
    absimlere.1
    imcld
    recnd
    subid1d
    3eqtrrd
    fveq2d
    wph
    cB
    cA
    @5
    absimlere.1
    abssubd
    3brtr4d
end
