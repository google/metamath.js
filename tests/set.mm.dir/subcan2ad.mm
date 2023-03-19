include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "subcan2.mm"
include "syl3anc.mm"

theorem subcan2ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A - C ) = ( B - C ) <-> A = B ) )

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
    cC
    cmin
    co
    cB
    cC
    cmin
    co
    wceq
    cA
    cB
    wceq
    wb
    negidd.1
    pncand.2
    subaddd.3
    cA
    cB
    cC
    subcan2
    syl3anc
end
