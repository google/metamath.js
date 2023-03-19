include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "subcan.mm"
include "syl3anc.mm"

theorem subcanad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A - B ) = ( A - C ) <-> B = C ) )

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
    cA
    cC
    cmin
    co
    wceq
    cB
    cC
    wceq
    wb
    negidd.1
    pncand.2
    subaddd.3
    cA
    cB
    cC
    subcan
    syl3anc
end
