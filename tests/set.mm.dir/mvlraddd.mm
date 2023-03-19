include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "pncand.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem mvlraddd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume mvlraddd.1: |- ( ph -> A e. CC )
  assume mvlraddd.2: |- ( ph -> B e. CC )
  assume mvlraddd.3: |- ( ph -> ( A + B ) = C )


  assert |- ( ph -> A = ( C - B ) )

  proof
    wph
    cA
    cB
    caddc
    co
    #
    cB
    cmin
    co
    cA
    cC
    cB
    cmin
    co
    wph
    cA
    cB
    mvlraddd.1
    mvlraddd.2
    pncand
    wph
    @0
    cC
    cB
    cmin
    mvlraddd.3
    oveq1d
    eqtr3d
end
