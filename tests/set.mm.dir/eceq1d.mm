include "wceq.mm"
include "cec.mm"
include "eceq1.mm"
include "syl.mm"

theorem eceq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume eceq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> [ A ] C = [ B ] C )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    cec
    cB
    cC
    cec
    wceq
    eceq1d.1
    cA
    cB
    cC
    eceq1
    syl
end
