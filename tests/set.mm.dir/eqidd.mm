include "wceq.mm"
include "eqid.mm"
include "a1i.mm"

theorem eqidd
  let wph: wff ph
  let cA: class A


  assert |- ( ph -> A = A )

  proof
    cA
    cA
    wceq
    wph
    cA
    eqid
    a1i
end
