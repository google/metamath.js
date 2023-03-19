include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "oveq1d.mm"
include "pncand.mm"
include "eqtrd.mm"

theorem mvrraddd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume mvrraddd.1: |- ( ph -> B e. CC )
  assume mvrraddd.2: |- ( ph -> C e. CC )
  assume mvrraddd.3: |- ( ph -> A = ( B + C ) )


  assert |- ( ph -> ( A - C ) = B )

  proof
    wph
    cA
    cC
    cmin
    co
    cB
    cC
    caddc
    co
    #
    cC
    cmin
    co
    cB
    wph
    cA
    @0
    cC
    cmin
    mvrraddd.3
    oveq1d
    wph
    cB
    cC
    mvrraddd.1
    mvrraddd.2
    pncand
    eqtrd
end
