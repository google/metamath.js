include "caddc.mm"
include "co.mm"
include "addcomd.mm"
include "eqtrd.mm"

theorem comraddd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume comraddd.1: |- ( ph -> B e. CC )
  assume comraddd.2: |- ( ph -> C e. CC )
  assume comraddd.3: |- ( ph -> A = ( B + C ) )


  assert |- ( ph -> A = ( C + B ) )

  proof
    wph
    cA
    cB
    cC
    caddc
    co
    cC
    cB
    caddc
    co
    comraddd.3
    wph
    cB
    cC
    comraddd.1
    comraddd.2
    addcomd
    eqtrd
end
