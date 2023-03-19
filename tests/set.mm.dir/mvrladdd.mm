include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "comraddd.mm"
include "oveq1d.mm"
include "pncand.mm"
include "eqtrd.mm"

theorem mvrladdd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let vx: setvar x
  assume mvrladdd.1: |- ( ph -> B e. CC )
  assume mvrladdd.2: |- ( ph -> C e. CC )
  assume mvrladdd.3: |- ( ph -> A = ( B + C ) )


  assert |- ( ph -> ( A - B ) = C )

  proof
    wph
    cA
    cB
    cmin
    co
    cC
    cB
    caddc
    co
    #
    cB
    cmin
    co
    cC
    wph
    cA
    @0
    cB
    cmin
    wph
    cA
    cB
    cC
    mvrladdd.1
    mvrladdd.2
    mvrladdd.3
    comraddd
    oveq1d
    wph
    cC
    cB
    mvrladdd.2
    mvrladdd.1
    pncand
    eqtrd
end
