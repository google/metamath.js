include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "subadd4.mm"
include "syl22anc.mm"

theorem subadd4d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )
  assume addsub4d.4: |- ( ph -> D e. CC )


  assert |- ( ph -> ( ( A - B ) - ( C - D ) ) = ( ( A + D ) - ( B + C ) ) )

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
    cmin
    co
    cC
    cD
    cmin
    co
    cmin
    co
    cA
    cD
    caddc
    co
    cB
    cC
    caddc
    co
    cmin
    co
    wceq
    negidd.1
    pncand.2
    subaddd.3
    addsub4d.4
    cA
    cB
    cC
    cD
    subadd4
    syl22anc
end
