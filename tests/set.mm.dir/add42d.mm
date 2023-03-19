include "cc.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "add42.mm"
include "syl22anc.mm"

theorem add42d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume addd.1: |- ( ph -> A e. CC )
  assume addd.2: |- ( ph -> B e. CC )
  assume addd.3: |- ( ph -> C e. CC )
  assume add4d.4: |- ( ph -> D e. CC )


  assert |- ( ph -> ( ( A + B ) + ( C + D ) ) = ( ( A + C ) + ( D + B ) ) )

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
    cD
    cc
    wcel
    cA
    cB
    caddc
    co
    cC
    cD
    caddc
    co
    caddc
    co
    cA
    cC
    caddc
    co
    cD
    cB
    caddc
    co
    caddc
    co
    wceq
    addd.1
    addd.2
    addd.3
    add4d.4
    cA
    cB
    cC
    cD
    add42
    syl22anc
end
