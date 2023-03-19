include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "subdi.mm"
include "syl3anc.mm"

theorem subdid
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume mulm1d.1: |- ( ph -> A e. CC )
  assume mulnegd.2: |- ( ph -> B e. CC )
  assume subdid.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( A x. ( B - C ) ) = ( ( A x. B ) - ( A x. C ) ) )

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
    cmul
    co
    cA
    cB
    cmul
    co
    cA
    cC
    cmul
    co
    cmin
    co
    wceq
    mulm1d.1
    mulnegd.2
    subdid.3
    cA
    cB
    cC
    subdi
    syl3anc
end
