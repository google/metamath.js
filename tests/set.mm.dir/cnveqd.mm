include "wceq.mm"
include "ccnv.mm"
include "cnveq.mm"
include "syl.mm"

theorem cnveqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume cnveqd.1: |- ( ph -> A = B )


  assert |- ( ph -> `' A = `' B )

  proof
    wph
    cA
    cB
    wceq
    cA
    ccnv
    cB
    ccnv
    wceq
    cnveqd.1
    cA
    cB
    cnveq
    syl
end
