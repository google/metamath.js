include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "wb.mm"
include "subadd2.mm"
include "syl3anc.mm"

theorem subadd2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )


  assert |- ( ph -> ( ( A - B ) = C <-> ( C + B ) = A ) )

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
    wceq
    cC
    cB
    caddc
    co
    cA
    wceq
    wb
    negidd.1
    pncand.2
    subaddd.3
    cA
    cB
    cC
    subadd2
    syl3anc
end
