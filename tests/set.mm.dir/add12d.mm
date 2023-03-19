include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "add12.mm"
include "syl3anc.mm"

theorem add12d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume addd.1: |- ( ph -> A e. CC )
  assume addd.2: |- ( ph -> B e. CC )
  assume addd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( A + ( B + C ) ) = ( B + ( A + C ) ) )

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
    cC
    caddc
    co
    caddc
    co
    cB
    cA
    cC
    caddc
    co
    caddc
    co
    wceq
    addd.1
    addd.2
    addd.3
    cA
    cB
    cC
    add12
    syl3anc
end
