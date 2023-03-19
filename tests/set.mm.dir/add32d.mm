include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "add32.mm"
include "syl3anc.mm"

theorem add32d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume addd.1: |- ( ph -> A e. CC )
  assume addd.2: |- ( ph -> B e. CC )
  assume addd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A + B ) + C ) = ( ( A + C ) + B ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    cc
    wcel
    cA
    cB
    caddc
    co
    cC
    caddc
    co
    cA
    cC
    caddc
    co
    cB
    caddc
    co
    wceq
    addd.1
    addd.2
    addd.3
    cA
    cB
    cC
    add32
    syl3anc
end
