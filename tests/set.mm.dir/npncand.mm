include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "caddc.mm"
include "wceq.mm"
include "npncan.mm"
include "syl3anc.mm"

theorem npncand
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A - B ) + ( B - C ) ) = ( A - C ) )

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
    cB
    cC
    cmin
    co
    caddc
    co
    cA
    cC
    cmin
    co
    wceq
    negidd.1
    pncand.2
    subaddd.3
    cA
    cB
    cC
    npncan
    syl3anc
end
