include "cmpt.mm"
include "cres.mm"
include "crli.mm"
include "resmptd.mm"
include "wbr.mm"
include "rlimres.mm"
include "syl.mm"
include "eqbrtrrd.mm"

theorem rlimres2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume rlimres2.1: |- ( ph -> A C_ B )
  assume rlimres2.2: |- ( ph -> ( x e. B |-> C ) ~~>r D )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( x e. A |-> C ) ~~>r D )

  proof
    wph
    vx
    cB
    cC
    cmpt
    #
    cA
    cres
    #
    vx
    cA
    cC
    cmpt
    cD
    crli
    wph
    vx
    cB
    cA
    cC
    rlimres2.1
    resmptd
    wph
    @0
    cD
    crli
    wbr
    @1
    cD
    crli
    wbr
    rlimres2.2
    cD
    cA
    @0
    rlimres
    syl
    eqbrtrrd
end
