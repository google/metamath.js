include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "nnncan.mm"
include "syl3anc.mm"

theorem nnncand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A - ( B - C ) ) - C ) = ( A - B ) )

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
    cmin
    co
    cmin
    co
    cC
    cmin
    co
    cA
    cB
    cmin
    co
    wceq
    negidd.1
    pncand.2
    subaddd.3
    cA
    cB
    cC
    nnncan
    syl3anc
end
