include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "nppcan3.mm"
include "syl3anc.mm"

theorem nppcan3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A - B ) + ( C + B ) ) = ( A + C ) )

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
    cmin
    co
    cC
    cB
    caddc
    co
    caddc
    co
    cA
    cC
    caddc
    co
    wceq
    negidd.1
    pncand.2
    subaddd.3
    cA
    cB
    cC
    nppcan3
    syl3anc
end
