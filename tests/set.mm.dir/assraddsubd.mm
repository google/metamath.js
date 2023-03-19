include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "addsubassd.mm"
include "eqtrd.mm"

theorem assraddsubd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vx: setvar x
  assume assraddsubd.1: |- ( ph -> B e. CC )
  assume assraddsubd.2: |- ( ph -> C e. CC )
  assume assraddsubd.3: |- ( ph -> D e. CC )
  assume assraddsubd.4: |- ( ph -> A = ( ( B + C ) - D ) )


  assert |- ( ph -> A = ( B + ( C - D ) ) )

  proof
    wph
    cA
    cB
    cC
    caddc
    co
    cD
    cmin
    co
    cB
    cC
    cD
    cmin
    co
    caddc
    co
    assraddsubd.4
    wph
    cB
    cC
    cD
    assraddsubd.1
    assraddsubd.2
    assraddsubd.3
    addsubassd
    eqtrd
end
