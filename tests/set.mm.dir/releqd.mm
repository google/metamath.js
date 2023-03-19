include "wceq.mm"
include "wrel.mm"
include "wb.mm"
include "releq.mm"
include "syl.mm"

theorem releqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume releqd.1: |- ( ph -> A = B )


  assert |- ( ph -> ( Rel A <-> Rel B ) )

  proof
    wph
    cA
    cB
    wceq
    cA
    wrel
    cB
    wrel
    wb
    releqd.1
    cA
    cB
    releq
    syl
end
